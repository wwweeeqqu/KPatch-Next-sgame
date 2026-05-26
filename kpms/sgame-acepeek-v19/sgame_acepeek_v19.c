/* SPDX-License-Identifier: GPL-2.0-or-later */
/* sgame-acepeek v19 — auto-detect sgame process by task->comm.
 *
 * Inherits all v18 functionality (fake-maps + mem-read + chmod-block + peek).
 * The single change: ace_sgame_tgid auto-updates whenever a syscall hook
 * fires from a task whose comm contains "tmgp.sgame". This removes the
 * stale-tgid hazard that caused sgame to die from an unguarded maps read
 * after each sgame restart.
 *
 * Fast path: tgid == ace_sgame_tgid -> hook continues.
 * Slow path: tgid mismatch -> check task->comm; if sgame, update tgid and
 *            continue; else skip.
 */

#include <compiler.h>
#include <kpmodule.h>
#include <linux/printk.h>
#include <linux/uaccess.h>
#include <linux/string.h>
#include <linux/sched.h>
#include <kputils.h>
#include <kallsyms.h>
#include <uapi/asm-generic/unistd.h>
#include <syscall.h>
#include <asm/ptrace.h>
#include <asm/current.h>

KPM_NAME("sgame-acepeek-v19");
KPM_VERSION("0.19.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("ctf");
KPM_DESCRIPTION("auto-detect sgame + fake maps + mem-read + ACE peek");

static __attribute__((noinline)) void *my_memset(void *s, int c, unsigned long n)
{ unsigned char *p=(unsigned char*)s; for(unsigned long i=0;i<n;i++)p[i]=(unsigned char)c; return s; }
static __attribute__((noinline)) void *my_memcpy(void *dst, const void *src, unsigned long n)
{ unsigned char *d=(unsigned char*)dst; const unsigned char *s=(const unsigned char*)src;
  for(unsigned long i=0;i<n;i++)d[i]=s[i]; return dst; }
#define memset my_memset
#define memcpy my_memcpy

struct pid; struct task_struct;
enum pid_type { PIDTYPE_PID, PIDTYPE_TGID, PIDTYPE_PGID, PIDTYPE_SID, PIDTYPE_MAX };
struct pid_namespace;

typedef pid_t (*task_pid_nr_ns_t)(struct task_struct *, enum pid_type, struct pid_namespace *);
typedef long (*copy_from_user_nofault_t)(void *, const void __user *, unsigned long);
typedef struct pid *(*find_get_pid_t)(pid_t);
typedef void (*put_pid_t)(struct pid *);
typedef struct task_struct *(*get_pid_task_t)(struct pid *, enum pid_type);
typedef int (*access_process_vm_t)(struct task_struct *, unsigned long, void *, int, unsigned int);

static task_pid_nr_ns_t task_pid_nr_ns_fn = 0;
static copy_from_user_nofault_t copy_from_user_nofault_fn = 0;
static find_get_pid_t find_get_pid_fn = 0;
static put_pid_t put_pid_fn = 0;
static get_pid_task_t get_pid_task_fn = 0;
static access_process_vm_t access_process_vm_fn = 0;

static volatile uint64_t total_openat = 0;
static volatile uint64_t fake_marked = 0;
static volatile uint64_t fake_filtered = 0;
static volatile uint64_t fake_lines_removed = 0;
static volatile uint64_t total_reads = 0, total_bytes = 0, fail_reads = 0;
static volatile uint64_t peek_recorded = 0;

#define OUTBUF_SZ 4096
static char g_outbuf[OUTBUF_SZ];
static volatile int g_busy = 0;

#define MAX_READ_LEN 2000
static unsigned char rb[MAX_READ_LEN];

static volatile pid_t ace_sgame_tgid = -1;

#define MAX_FAKE_FDS 64
struct fake_fd_entry {
    pid_t tid;
    int fd;
    int active;
};
static struct fake_fd_entry fake_fds[MAX_FAKE_FDS];
static volatile int fake_fds_lock = 0;

#define FILTER_BUF_SZ 8192
static char filter_in[FILTER_BUF_SZ];
static char filter_out[FILTER_BUF_SZ];

/* === v18 NEW: peek ring buffer for ACE register state === */
#define PEEK_RING_SZ 32
#define PEEK_FN_LEN  64
#define PEEK_STACK_BYTES 256
struct peek_event {
    uint64_t seq;
    uint64_t regs[31];        /* x0..x30 */
    uint64_t sp;
    uint64_t pc;
    uint64_t stack[PEEK_STACK_BYTES / 8];
    int32_t  pid;
    int32_t  tid;
    char     filename[PEEK_FN_LEN];
};
static struct peek_event peek_ring[PEEK_RING_SZ];
static volatile uint32_t peek_head = 0;

static int str_contains(const char *s, int n, const char *needle)
{
    int nl = 0; while (needle[nl]) nl++;
    if (n < nl) return 0;
    for (int i = 0; i + nl <= n; i++) {
        int j; for (j = 0; j < nl; j++) if (s[i+j] != needle[j]) break;
        if (j == nl) return 1;
    }
    return 0;
}

static int path_contains_sgame(const char *p, int n)
{
    const char *needle = "com.tencent.tmgp.sgame";
    int nl = 22;
    for (int i = 0; i + nl <= n; i++) {
        int j; for (j = 0; j < nl; j++) if (p[i+j] != needle[j]) break;
        if (j == nl) return 1;
    }
    return 0;
}

/* v19: detect sgame via task->comm.
 *
 * Android app processes get their comm set by Bionic to the cmdline
 * truncated to TASK_COMM_LEN-1 (15 chars). For "com.tencent.tmgp.sgame"
 * the comm is typically "tmgp.sgame" (10 chars). We match the unique
 * "tmgp.sgame" substring.
 */
static int comm_is_sgame(const char *comm)
{
    return str_contains(comm, TASK_COMM_LEN, "tmgp.sgame");
}

/* Return 1 if `current` is an sgame task (and atomically update
 * ace_sgame_tgid to its tgid). Return 0 otherwise.
 *
 * Fast path: tgid == ace_sgame_tgid -> immediate yes.
 * Slow path: tgid mismatch -> check comm; on match, adopt the new tgid.
 */
static int is_or_become_sgame(void)
{
    if (!task_pid_nr_ns_fn) return 0;
    struct task_struct *task = current;
    pid_t tgid = task_pid_nr_ns_fn(task, PIDTYPE_TGID, 0);
    if (tgid <= 0) return 0;
    if (tgid == ace_sgame_tgid) return 1;
    const char *comm = get_task_comm(task);
    if (!comm) return 0;
    if (!comm_is_sgame(comm)) return 0;
    ace_sgame_tgid = tgid;
    return 1;
}

static int line_is_suspicious(const char *line, int len)
{
    if (str_contains(line, len, "/data/adb")) return 1;
    if (str_contains(line, len, "zygisk")) return 1;
    if (str_contains(line, len, "frida")) return 1;
    if (str_contains(line, len, "magisk")) return 1;
    if (str_contains(line, len, "ksu")) return 1;
    if (str_contains(line, len, "KernelSU")) return 1;
    if (str_contains(line, len, "kpatch")) return 1;
    if (str_contains(line, len, "KPatch")) return 1;
    if (str_contains(line, len, "supolicy")) return 1;
    return 0;
}

static void before_fchmodat(hook_fargs3_t *args, void *udata)
{
    const char __user *filename = (const char __user *)syscall_argn(args, 1);
    if (!filename) return;
    char buf[256];
    long n = compat_strncpy_from_user(buf, filename, sizeof(buf) - 1);
    if (n <= 0) return;
    if (n > (long)sizeof(buf) - 1) n = sizeof(buf) - 1;
    buf[n] = 0;
    int len = 0; while (len < (int)sizeof(buf) && buf[len]) len++;
    if (path_contains_sgame(buf, len)) {
        args->skip_origin = 1;
        args->ret = 0;
    }
}

/* before_openat — peek registers when path is /maps */
static void before_openat(hook_fargs4_t *args, void *udata)
{
    total_openat++;
    if (!is_or_become_sgame()) return;
    struct task_struct *task = current;
    pid_t tgid = ace_sgame_tgid;

    const char __user *filename = (const char __user *)syscall_argn(args, 1);
    if (!filename) return;
    char fnbuf[PEEK_FN_LEN];
    long n = compat_strncpy_from_user(fnbuf, filename, sizeof(fnbuf) - 1);
    if (n <= 0) return;
    if (n > (long)sizeof(fnbuf) - 1) n = sizeof(fnbuf) - 1;
    fnbuf[n] = 0;
    int len = 0; while (len < (int)sizeof(fnbuf) && fnbuf[len]) len++;
    if (!str_contains(fnbuf, len, "/maps")) return;

    struct pt_regs *regs = (struct pt_regs *)args->args[0];
    if (!regs) return;

    /* record peek event */
    uint32_t idx = __sync_fetch_and_add(&peek_head, 1) % PEEK_RING_SZ;
    struct peek_event *ev = &peek_ring[idx];
    ev->seq = peek_recorded++;
    for (int i = 0; i < 31; i++) ev->regs[i] = regs->regs[i];
    ev->sp = regs->sp;
    ev->pc = regs->pc;
    ev->pid = tgid;
    ev->tid = task_pid_nr_ns_fn(task, PIDTYPE_PID, 0);
    my_memcpy(ev->filename, fnbuf, len + 1);
    /* try to dump stack content */
    if (copy_from_user_nofault_fn && regs->sp) {
        copy_from_user_nofault_fn(ev->stack, (const void __user *)regs->sp, PEEK_STACK_BYTES);
    }
}

/* after_openat — fake-maps fd marking */
static void after_openat(hook_fargs4_t *args, void *udata)
{
    int64_t ret = (int64_t)args->ret;
    if (ret < 0) return;
    if (!is_or_become_sgame()) return;
    struct task_struct *task = current;

    const char __user *filename = (const char __user *)syscall_argn(args, 1);
    if (!filename) return;
    char fnbuf[PEEK_FN_LEN];
    long n = compat_strncpy_from_user(fnbuf, filename, sizeof(fnbuf) - 1);
    if (n <= 0) return;
    if (n > (long)sizeof(fnbuf) - 1) n = sizeof(fnbuf) - 1;
    fnbuf[n] = 0;
    int len = 0; while (len < (int)sizeof(fnbuf) && fnbuf[len]) len++;
    if (!str_contains(fnbuf, len, "/maps")) return;

    pid_t tid = task_pid_nr_ns_fn(task, PIDTYPE_PID, 0);
    int fd = (int)ret;
    while (__sync_lock_test_and_set(&fake_fds_lock, 1)) ;
    int slot = -1;
    for (int i = 0; i < MAX_FAKE_FDS; i++) {
        if (!fake_fds[i].active) { slot = i; break; }
    }
    if (slot >= 0) {
        fake_fds[slot].tid = tid;
        fake_fds[slot].fd = fd;
        fake_fds[slot].active = 1;
        fake_marked++;
    }
    __sync_lock_release(&fake_fds_lock);
}

static void after_read(hook_fargs3_t *args, void *udata)
{
    int64_t ret = (int64_t)args->ret;
    if (ret <= 0) return;
    if (ret > FILTER_BUF_SZ) return;
    if (!is_or_become_sgame()) return;
    struct task_struct *task = current;

    int fd = (int)syscall_argn(args, 0);
    pid_t tid = task_pid_nr_ns_fn(task, PIDTYPE_PID, 0);
    int is_fake = 0;
    while (__sync_lock_test_and_set(&fake_fds_lock, 1)) ;
    for (int i = 0; i < MAX_FAKE_FDS; i++) {
        if (fake_fds[i].active && fake_fds[i].tid == tid && fake_fds[i].fd == fd) {
            is_fake = 1; break;
        }
    }
    __sync_lock_release(&fake_fds_lock);
    if (!is_fake) return;

    void __user *ubuf = (void __user *)syscall_argn(args, 1);
    if (!ubuf || !copy_from_user_nofault_fn) return;
    long n2 = copy_from_user_nofault_fn(filter_in, ubuf, (unsigned long)ret);
    if (n2 != 0) return;

    int out_pos = 0;
    int line_start = 0;
    int lines_dropped = 0;
    for (int i = 0; i < (int)ret; i++) {
        if (filter_in[i] == '\n') {
            int line_len = i - line_start + 1;
            if (!line_is_suspicious(filter_in + line_start, line_len)) {
                if (out_pos + line_len <= FILTER_BUF_SZ) {
                    my_memcpy(filter_out + out_pos, filter_in + line_start, line_len);
                    out_pos += line_len;
                }
            } else {
                lines_dropped++;
            }
            line_start = i + 1;
        }
    }
    if (line_start < (int)ret) {
        int line_len = (int)ret - line_start;
        if (!line_is_suspicious(filter_in + line_start, line_len)) {
            if (out_pos + line_len <= FILTER_BUF_SZ) {
                my_memcpy(filter_out + out_pos, filter_in + line_start, line_len);
                out_pos += line_len;
            }
        } else {
            lines_dropped++;
        }
    }
    if (lines_dropped == 0) return;
    compat_copy_to_user(ubuf, filter_out, out_pos);
    args->ret = out_pos;
    fake_filtered++;
    fake_lines_removed += lines_dropped;
}

static void before_close(hook_fargs1_t *args, void *udata)
{
    if (!is_or_become_sgame()) return;
    struct task_struct *task = current;
    int fd = (int)syscall_argn(args, 0);
    pid_t tid = task_pid_nr_ns_fn(task, PIDTYPE_PID, 0);
    while (__sync_lock_test_and_set(&fake_fds_lock, 1)) ;
    for (int i = 0; i < MAX_FAKE_FDS; i++) {
        if (fake_fds[i].active && fake_fds[i].tid == tid && fake_fds[i].fd == fd) {
            fake_fds[i].active = 0;
            break;
        }
    }
    __sync_lock_release(&fake_fds_lock);
}

static pid_t parse_dec(const char **sp) {
    const char *s = *sp; while (*s == ' ') s++;
    pid_t v = 0; while (*s >= '0' && *s <= '9') { v = v*10 + (*s-'0'); s++; }
    *sp = s; return v;
}
static uint64_t parse_hex(const char **sp) {
    const char *s = *sp; while (*s == ' ') s++;
    if (s[0]=='0' && (s[1]=='x' || s[1]=='X')) s += 2;
    uint64_t v = 0;
    while (1) { char c = *s;
        if (c>='0'&&c<='9') v=v*16+(c-'0');
        else if (c>='a'&&c<='f') v=v*16+(c-'a'+10);
        else if (c>='A'&&c<='F') v=v*16+(c-'A'+10);
        else break; s++; }
    *sp = s; return v;
}
static int u64_to_str(uint64_t v, char *out) {
    if (v==0){out[0]='0';return 1;}
    char rev[24]; int ri=0; while(v){rev[ri++]='0'+(v%10);v/=10;}
    for(int i=0;i<ri;i++)out[i]=rev[ri-1-i]; return ri;
}
static int u64_to_hex(uint64_t v, char *out) {
    static const char hex[] = "0123456789abcdef";
    if (v == 0) { out[0]='0'; return 1; }
    char rev[24]; int ri=0;
    while (v) { rev[ri++] = hex[v&0xf]; v >>= 4; }
    for (int i=0;i<ri;i++) out[i]=rev[ri-1-i];
    return ri;
}

static long sgs_ctl0(const char *args, char *__user out_msg, int outlen)
{
    if (__sync_lock_test_and_set(&g_busy, 1)) {
        const char *m="E:busy\n"; compat_copy_to_user(out_msg, m, 8); return -1;
    }
    long rc = -1;

    if (!args || args[0] == 0 || args[0]=='s') {
        char *buf = g_outbuf; int n=0;
        const char *p="openat="; while(*p)buf[n++]=*p++;
        n += u64_to_str(total_openat, buf+n); buf[n++]=' ';
        p="marked="; while(*p)buf[n++]=*p++;
        n += u64_to_str(fake_marked, buf+n); buf[n++]=' ';
        p="filtered="; while(*p)buf[n++]=*p++;
        n += u64_to_str(fake_filtered, buf+n); buf[n++]=' ';
        p="lines_removed="; while(*p)buf[n++]=*p++;
        n += u64_to_str(fake_lines_removed, buf+n); buf[n++]=' ';
        p="reads="; while(*p)buf[n++]=*p++;
        n += u64_to_str(total_reads, buf+n); buf[n++]=' ';
        p="peek="; while(*p)buf[n++]=*p++;
        n += u64_to_str(peek_recorded, buf+n); buf[n++]=' ';
        p="sgame_tgid="; while(*p)buf[n++]=*p++;
        n += u64_to_str((uint64_t)(ace_sgame_tgid > 0 ? ace_sgame_tgid : 0), buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    if (args[0]=='p' && args[1]==' ') {
        const char *p = args + 2;
        pid_t tgid = parse_dec(&p);
        ace_sgame_tgid = tgid;
        char *buf = g_outbuf; int n = 0;
        const char *m = "P:tgid="; while (*m) buf[n++] = *m++;
        n += u64_to_str((uint64_t)tgid, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    if (args[0]=='c') {
        for (int i = 0; i < MAX_FAKE_FDS; i++) fake_fds[i].active = 0;
        for (int i = 0; i < PEEK_RING_SZ; i++) peek_ring[i].seq = 0;
        peek_head = 0; peek_recorded = 0;
        total_openat = 0; fake_marked = 0; fake_filtered = 0; fake_lines_removed = 0;
        total_reads = 0; total_bytes = 0; fail_reads = 0;
        const char *m="C:cleared\n"; compat_copy_to_user(out_msg, m, 11);
        rc = 0;
        goto out;
    }
    /* 'r <pid> <addr> <len>' — cross-process mem-read */
    if (args[0]=='r' && args[1]==' ') {
        const char *p = args + 2;
        pid_t pid = parse_dec(&p);
        uint64_t addr = parse_hex(&p);
        uint64_t len = parse_hex(&p);
        if (pid==0||addr==0||len==0||len>MAX_READ_LEN){
            const char *m="E:bad_args\n"; compat_copy_to_user(out_msg, m, 12); goto out;
        }
        if (addr >= 0x800000000000UL){
            const char *m="E:bad_addr\n"; compat_copy_to_user(out_msg, m, 12); goto out;
        }
        if (!find_get_pid_fn || !get_pid_task_fn || !access_process_vm_fn) {
            const char *m="E:fns_null\n"; compat_copy_to_user(out_msg, m, 12); goto out;
        }
        struct pid *pp = find_get_pid_fn(pid);
        if (!pp){ const char *m="E:nopid\n"; compat_copy_to_user(out_msg, m, 9); goto out; }
        struct task_struct *tsk = get_pid_task_fn(pp, PIDTYPE_PID);
        if (put_pid_fn) put_pid_fn(pp);
        if (!tsk){ const char *m="E:notsk\n"; compat_copy_to_user(out_msg, m, 9); goto out; }
        int r = access_process_vm_fn(tsk, (unsigned long)addr, rb, (int)len, 0);
        if (r <= 0){ fail_reads++; const char *m="E:read_fail\n"; compat_copy_to_user(out_msg, m, 13); goto out; }
        total_reads++; total_bytes += r;
        static const char hex[] = "0123456789abcdef";
        char *buf = g_outbuf; my_memset(buf, 0, OUTBUF_SZ);
        int n=0; buf[n++]='R'; buf[n++]=':';
        n += u64_to_str((uint64_t)r, buf+n); buf[n++]=' ';
        int max_hex = OUTBUF_SZ - n - 4;
        int actual = r*2 > max_hex ? max_hex/2 : r;
        for (int i=0;i<actual;i++){
            unsigned char b = rb[i];
            buf[n++] = hex[b>>4]; buf[n++] = hex[b&0xf];
        }
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    /* 'e <idx>' — dump one peek event (regs only, 31*8 + sp + pc = 264 bytes -> 528 hex) */
    if (args[0]=='e' && args[1]==' ') {
        const char *p = args + 2;
        uint64_t idx_h = parse_hex(&p);
        if (idx_h >= PEEK_RING_SZ) {
            const char *m="E:bad_idx\n"; compat_copy_to_user(out_msg, m, 11); goto out;
        }
        struct peek_event *ev = &peek_ring[idx_h];
        char *buf = g_outbuf; my_memset(buf, 0, OUTBUF_SZ);
        int n=0; buf[n++]='E'; buf[n++]=':';
        n += u64_to_str(ev->seq, buf+n); buf[n++]=' ';
        n += u64_to_str((uint64_t)ev->pid, buf+n); buf[n++]=' ';
        n += u64_to_str((uint64_t)ev->tid, buf+n); buf[n++]=' ';
        int fl = 0; while (fl < PEEK_FN_LEN && ev->filename[fl]) {
            if (n >= OUTBUF_SZ - 800) break;
            buf[n++] = ev->filename[fl++];
        }
        buf[n++]=' ';
        /* regs x0..x30 (31), sp, pc as hex */
        for (int i = 0; i < 31; i++) {
            n += u64_to_hex(ev->regs[i], buf+n); buf[n++]=',';
        }
        n += u64_to_hex(ev->sp, buf+n); buf[n++]=',';
        n += u64_to_hex(ev->pc, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    /* 'k <idx>' — dump peek event stack (256 bytes -> 512 hex chars) */
    if (args[0]=='k' && args[1]==' ') {
        const char *p = args + 2;
        uint64_t idx_h = parse_hex(&p);
        if (idx_h >= PEEK_RING_SZ) {
            const char *m="E:bad_idx\n"; compat_copy_to_user(out_msg, m, 11); goto out;
        }
        struct peek_event *ev = &peek_ring[idx_h];
        char *buf = g_outbuf; my_memset(buf, 0, OUTBUF_SZ);
        int n=0; buf[n++]='K'; buf[n++]=':';
        n += u64_to_str(ev->seq, buf+n); buf[n++]=' ';
        n += u64_to_hex(ev->sp, buf+n); buf[n++]=' ';
        /* stack content as hex */
        unsigned char *sb = (unsigned char *)ev->stack;
        for (int i = 0; i < PEEK_STACK_BYTES; i++) {
            if (n >= OUTBUF_SZ - 4) break;
            unsigned char b = sb[i];
            static const char hex[] = "0123456789abcdef";
            buf[n++] = hex[b>>4]; buf[n++] = hex[b&0xf];
        }
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    {
        const char *m="E:unknown_cmd\n";
        compat_copy_to_user(out_msg, m, 15);
    }
out:
    __sync_lock_release(&g_busy);
    return rc;
}

static long sgs_init(const char *args, const char *event, void *__user reserved)
{
    pr_info("[acepeek-v18] init\n");
    task_pid_nr_ns_fn = (task_pid_nr_ns_t)kallsyms_lookup_name("__task_pid_nr_ns");
    copy_from_user_nofault_fn = (copy_from_user_nofault_t)kallsyms_lookup_name("copy_from_user_nofault");
    if (!copy_from_user_nofault_fn)
        copy_from_user_nofault_fn = (copy_from_user_nofault_t)kallsyms_lookup_name("__copy_from_user_inatomic");
    find_get_pid_fn = (find_get_pid_t)kallsyms_lookup_name("find_get_pid");
    put_pid_fn = (put_pid_t)kallsyms_lookup_name("put_pid");
    get_pid_task_fn = (get_pid_task_t)kallsyms_lookup_name("get_pid_task");
    access_process_vm_fn = (access_process_vm_t)kallsyms_lookup_name("access_process_vm");
    pr_info("[acepeek-v18] fns ok\n");

    for (int i = 0; i < MAX_FAKE_FDS; i++) fake_fds[i].active = 0;
    for (int i = 0; i < PEEK_RING_SZ; i++) peek_ring[i].seq = 0;

    hook_err_t e1 = inline_hook_syscalln(__NR_fchmodat, 3, before_fchmodat, 0, 0);
    hook_err_t e2 = inline_hook_syscalln(__NR_openat, 4, before_openat, after_openat, 0);
    hook_err_t e3 = inline_hook_syscalln(__NR_read, 3, 0, after_read, 0);
    hook_err_t e4 = inline_hook_syscalln(__NR_close, 1, before_close, 0, 0);
    pr_info("[acepeek-v18] hook err: %d %d %d %d\n", e1, e2, e3, e4);
    return 0;
}

static long sgs_exit(void *__user reserved)
{
    inline_unhook_syscalln(__NR_fchmodat, before_fchmodat, 0);
    inline_unhook_syscalln(__NR_openat, before_openat, after_openat);
    inline_unhook_syscalln(__NR_read, 0, after_read);
    inline_unhook_syscalln(__NR_close, before_close, 0);
    pr_info("[acepeek-v18] exit peek_recorded=%llu\n", peek_recorded);
    return 0;
}

KPM_INIT(sgs_init);
KPM_CTL0(sgs_ctl0);
KPM_EXIT(sgs_exit);
