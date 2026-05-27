/* SPDX-License-Identifier: GPL-2.0-or-later */
/* sgame-fakemem v18 — v17 + root-marker hide path (仿 LQ_hide_path_cmd).
 *
 * v17 已有: fake /proc/maps + cross-process mem-read
 *
 * v18 新增:
 *   - hook faccessat / faccessat2 / newfstatat / statx
 *   - 已 hook openat 加 hide 逻辑
 *   - hook getdents64 过滤目录项
 *   - 对 sgame_tgid 调用且路径在 hide list 时, 返回 -ENOENT
 *
 * 目的: 让 sgame 反作弊扫不到 root marker (/system/bin/su, /data/adb,
 * /sys/module/ksu, /sys/module/kpatch, /dev/.ksu* 等). 否则即使我们
 * mount-bind libtersafe.so 让反作弊废掉, sgame 仍会上报"设备 root" 给服务器
 * 触发软降级 (实测 2026-05-27 PJF110 + SukiSU).
 *
 * ctl commands:
 *   s                       — status
 *   p <tgid>                — set sgame tgid (for fake-fd + hide)
 *   c                       — clear counters + fd table
 *   r <pid> <addr> <len>    — read sgame memory (v14 carry-over)
 *   h <path>                — add path to hide list (新增 v18)
 *   H                       — clear hide list (新增 v18)
 *   l                       — list hide paths (新增 v18)
 */

#include <compiler.h>
#include <kpmodule.h>
#include <linux/printk.h>
#include <linux/uaccess.h>
#include <linux/string.h>
#include <kputils.h>
#include <kallsyms.h>
#include <uapi/asm-generic/unistd.h>
#include <syscall.h>
#include <asm/ptrace.h>
#include <asm/current.h>

KPM_NAME("sgame-fakemem-v20");
KPM_VERSION("0.20.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("ctf");
KPM_DESCRIPTION("v17 + hide root marker paths (faccessat/newfstatat/openat/getdents64)");

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
static volatile uint64_t hide_blocks_access = 0;
static volatile uint64_t hide_blocks_stat = 0;
static volatile uint64_t hide_blocks_open = 0;

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

/* === v18 hide path table === */
#define MAX_HIDE_PATHS 32
#define MAX_HIDE_PATH_LEN 96
static char hide_paths[MAX_HIDE_PATHS][MAX_HIDE_PATH_LEN];
static int hide_paths_len[MAX_HIDE_PATHS];
static int hide_paths_count = 0;
static volatile int hide_lock = 0;

/* === v19 syscall trace ring buffer === */
#define TRACE_BUF_SZ 32768
static char trace_buf[TRACE_BUF_SZ];
static volatile int trace_pos = 0;
static volatile int trace_wrapped = 0;
static volatile int trace_lock = 0;
static volatile uint64_t trace_total = 0;
static volatile int trace_enabled = 1;

static void trace_event(const char *sc, const char *path, int path_len)
{
    if (!trace_enabled) return;
    int sc_len = 0; while (sc[sc_len]) sc_len++;
    int total = sc_len + 1 + path_len + 1;
    if (total > 200) return;
    while (__sync_lock_test_and_set(&trace_lock, 1)) ;
    if (trace_pos + total > TRACE_BUF_SZ) {
        trace_pos = 0;
        trace_wrapped = 1;
    }
    for (int i = 0; i < sc_len; i++) trace_buf[trace_pos++] = sc[i];
    trace_buf[trace_pos++] = ':';
    for (int i = 0; i < path_len; i++) trace_buf[trace_pos++] = path[i];
    trace_buf[trace_pos++] = '\n';
    trace_total++;
    __sync_lock_release(&trace_lock);
}

static int str_eq(const char *a, const char *b) {
    while (*a && *b) { if (*a != *b) return 0; a++; b++; }
    return *a == 0 && *b == 0;
}

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
    /* v20 bugfix: NOT filter "libtersafe" — sgame 自检会读 maps 找
     * libtersafe.so, 若被过滤掉则触发 client 自杀闪退 (test_B/test_C 实测).
     * 我们不 mount-bind libtersafe.so 路径 anti-cheat 正常运行不被 server 降级.
     */
    return 0;
}

/* === v18: 检查 path 是否在 hide list ===
 * 匹配规则: path == hide_entry 或 path 以 hide_entry/ 开头
 * 例如 hide_entry="/data/adb" 会匹配 /data/adb 和 /data/adb/ksu 但不匹配 /data/adb_other
 */
static int path_is_hidden(const char *path, int len)
{
    if (len <= 0) return 0;
    for (int i = 0; i < hide_paths_count; i++) {
        int hl = hide_paths_len[i];
        if (len < hl) continue;
        int j; for (j = 0; j < hl; j++) if (path[j] != hide_paths[i][j]) break;
        if (j != hl) continue;
        if (len == hl) return 1;
        if (path[hl] == '/') return 1;
    }
    return 0;
}

/* === v17 hooks 保留 === */

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

static void after_openat(hook_fargs4_t *args, void *udata)
{
    total_openat++;
    int64_t ret = (int64_t)args->ret;
    if (ret < 0) return;
    if (ace_sgame_tgid <= 0) return;
    if (!task_pid_nr_ns_fn) return;
    struct task_struct *task = current;
    pid_t tgid = task_pid_nr_ns_fn(task, PIDTYPE_TGID, 0);
    if (tgid != ace_sgame_tgid) return;

    const char __user *filename = (const char __user *)syscall_argn(args, 1);
    if (!filename) return;
    char fnbuf[96];
    long n = compat_strncpy_from_user(fnbuf, filename, sizeof(fnbuf) - 1);
    if (n <= 0) return;
    if (n > (long)sizeof(fnbuf) - 1) n = sizeof(fnbuf) - 1;
    fnbuf[n] = 0;
    int len = 0; while (len < (int)sizeof(fnbuf) && fnbuf[len]) len++;
    /* v18: 同时拦截 /maps 和 /mountinfo 让 after_read 走过滤 */
    int is_maps = str_contains(fnbuf, len, "/maps");
    int is_mountinfo = str_contains(fnbuf, len, "/mountinfo");
    if (!is_maps && !is_mountinfo) return;

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
    if (ace_sgame_tgid <= 0) return;
    if (!task_pid_nr_ns_fn) return;
    struct task_struct *task = current;
    pid_t tgid = task_pid_nr_ns_fn(task, PIDTYPE_TGID, 0);
    if (tgid != ace_sgame_tgid) return;

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
    if (ace_sgame_tgid <= 0) return;
    if (!task_pid_nr_ns_fn) return;
    struct task_struct *task = current;
    pid_t tgid = task_pid_nr_ns_fn(task, PIDTYPE_TGID, 0);
    if (tgid != ace_sgame_tgid) return;
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

/* === v18 新增 hide hooks === */

static int is_sgame_caller(void) {
    if (ace_sgame_tgid <= 0) return 0;
    if (!task_pid_nr_ns_fn) return 0;
    struct task_struct *task = current;
    pid_t tgid = task_pid_nr_ns_fn(task, PIDTYPE_TGID, 0);
    return tgid == ace_sgame_tgid;
}

/* 读 user 路径到 kernel buf */
static int read_user_path(const char __user *p, char *out, int max) {
    if (!p) return 0;
    long n = compat_strncpy_from_user(out, p, max - 1);
    if (n <= 0) return 0;
    if (n > max - 1) n = max - 1;
    out[n] = 0;
    int len = 0; while (len < max && out[len]) len++;
    return len;
}

/* before_faccessat: int faccessat(int dirfd, const char *path, int mode) */
static void before_faccessat(hook_fargs3_t *args, void *udata)
{
    if (!is_sgame_caller()) return;
    char buf[128];
    int len = read_user_path((const char __user *)syscall_argn(args, 1), buf, sizeof(buf));
    if (len == 0) return;
    trace_event("access", buf, len);
    if (path_is_hidden(buf, len)) {
        args->skip_origin = 1;
        args->ret = -2;
        hide_blocks_access++;
    }
}

/* before_faccessat2: int faccessat2(int dirfd, const char *path, int mode, int flags) */
static void before_faccessat2(hook_fargs4_t *args, void *udata)
{
    if (!is_sgame_caller()) return;
    char buf[128];
    int len = read_user_path((const char __user *)syscall_argn(args, 1), buf, sizeof(buf));
    if (len == 0) return;
    trace_event("acces2", buf, len);
    if (path_is_hidden(buf, len)) {
        args->skip_origin = 1;
        args->ret = -2;
        hide_blocks_access++;
    }
}

/* before_newfstatat: int newfstatat(int dirfd, const char *path, struct stat *buf, int flags) */
static void before_newfstatat(hook_fargs4_t *args, void *udata)
{
    if (!is_sgame_caller()) return;
    char buf[128];
    int len = read_user_path((const char __user *)syscall_argn(args, 1), buf, sizeof(buf));
    if (len == 0) return;
    trace_event("stat", buf, len);
    if (path_is_hidden(buf, len)) {
        args->skip_origin = 1;
        args->ret = -2;
        hide_blocks_stat++;
    }
}

/* before_statx: int statx(int dirfd, const char *path, int flags, mask, struct statx *buf) */
static void before_statx(hook_fargs4_t *args, void *udata)
{
    if (!is_sgame_caller()) return;
    char buf[128];
    int len = read_user_path((const char __user *)syscall_argn(args, 1), buf, sizeof(buf));
    if (len == 0) return;
    trace_event("statx", buf, len);
    if (path_is_hidden(buf, len)) {
        args->skip_origin = 1;
        args->ret = -2;
        hide_blocks_stat++;
    }
}

/* before_openat_hide: 在原 after_openat 之前增加 hide 拦截 */
static void before_openat_hide(hook_fargs4_t *args, void *udata)
{
    if (!is_sgame_caller()) return;
    char buf[128];
    int len = read_user_path((const char __user *)syscall_argn(args, 1), buf, sizeof(buf));
    if (len == 0) return;
    trace_event("open", buf, len);
    if (path_is_hidden(buf, len)) {
        args->skip_origin = 1;
        args->ret = -2;
        hide_blocks_open++;
    }
}

/* === ctl0 === */

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
        p="bytes="; while(*p)buf[n++]=*p++;
        n += u64_to_str(total_bytes, buf+n); buf[n++]=' ';
        p="fail="; while(*p)buf[n++]=*p++;
        n += u64_to_str(fail_reads, buf+n); buf[n++]=' ';
        p="hide_access="; while(*p)buf[n++]=*p++;
        n += u64_to_str(hide_blocks_access, buf+n); buf[n++]=' ';
        p="hide_stat="; while(*p)buf[n++]=*p++;
        n += u64_to_str(hide_blocks_stat, buf+n); buf[n++]=' ';
        p="hide_open="; while(*p)buf[n++]=*p++;
        n += u64_to_str(hide_blocks_open, buf+n); buf[n++]=' ';
        p="hide_count="; while(*p)buf[n++]=*p++;
        n += u64_to_str((uint64_t)hide_paths_count, buf+n); buf[n++]=' ';
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
        total_openat = 0; fake_marked = 0; fake_filtered = 0; fake_lines_removed = 0;
        total_reads = 0; total_bytes = 0; fail_reads = 0;
        hide_blocks_access = 0; hide_blocks_stat = 0; hide_blocks_open = 0;
        const char *m="C:cleared\n"; compat_copy_to_user(out_msg, m, 11);
        rc = 0;
        goto out;
    }
    /* h <path> — add path to hide list */
    if (args[0]=='h' && args[1]==' ') {
        const char *p = args + 2;
        while (*p == ' ') p++;
        int len = 0;
        while (p[len] && p[len] != '\n' && p[len] != ' ' && len < MAX_HIDE_PATH_LEN - 1) len++;
        if (len == 0) {
            const char *m="E:empty_path\n"; compat_copy_to_user(out_msg, m, 14); goto out;
        }
        while (__sync_lock_test_and_set(&hide_lock, 1)) ;
        if (hide_paths_count >= MAX_HIDE_PATHS) {
            __sync_lock_release(&hide_lock);
            const char *m="E:hide_full\n"; compat_copy_to_user(out_msg, m, 13); goto out;
        }
        int idx = hide_paths_count;
        for (int i = 0; i < len; i++) hide_paths[idx][i] = p[i];
        hide_paths[idx][len] = 0;
        hide_paths_len[idx] = len;
        hide_paths_count++;
        __sync_lock_release(&hide_lock);
        char *buf = g_outbuf; int n = 0;
        const char *m = "H:added "; while (*m) buf[n++] = *m++;
        for (int i = 0; i < len; i++) buf[n++] = p[i];
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    /* H — clear hide list */
    if (args[0]=='H' && (args[1] == 0 || args[1] == '\n')) {
        while (__sync_lock_test_and_set(&hide_lock, 1)) ;
        hide_paths_count = 0;
        __sync_lock_release(&hide_lock);
        const char *m="H:cleared\n"; compat_copy_to_user(out_msg, m, 11);
        rc = 0;
        goto out;
    }
    /* v19: L — dump syscall trace ring buffer */
    if (args[0]=='L' && (args[1] == 0 || args[1] == '\n')) {
        char *buf = g_outbuf; int n = 0;
        const char *m="T:"; while(*m)buf[n++]=*m++;
        n += u64_to_str(trace_total, buf+n);
        buf[n++] = ' ';
        m="wrapped="; while(*m)buf[n++]=*m++;
        n += u64_to_str((uint64_t)trace_wrapped, buf+n);
        buf[n++] = ' ';
        m="pos="; while(*m)buf[n++]=*m++;
        n += u64_to_str((uint64_t)trace_pos, buf+n);
        buf[n++] = '\n';
        while (__sync_lock_test_and_set(&trace_lock, 1)) ;
        int max_copy = OUTBUF_SZ - n - 4;
        int copy = (trace_pos < max_copy) ? trace_pos : max_copy;
        for (int i = 0; i < copy; i++) buf[n++] = trace_buf[i];
        __sync_lock_release(&trace_lock);
        buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    /* v19: D — clear trace buffer */
    if (args[0]=='D' && (args[1] == 0 || args[1] == '\n')) {
        while (__sync_lock_test_and_set(&trace_lock, 1)) ;
        trace_pos = 0;
        trace_wrapped = 0;
        trace_total = 0;
        __sync_lock_release(&trace_lock);
        const char *m="D:cleared\n"; compat_copy_to_user(out_msg, m, 11);
        rc = 0;
        goto out;
    }
    /* v19: T 0/1 — disable/enable trace */
    if (args[0]=='T' && args[1]==' ') {
        trace_enabled = (args[2] == '1') ? 1 : 0;
        char *buf = g_outbuf; int n = 0;
        const char *m="T:enabled="; while(*m)buf[n++]=*m++;
        n += u64_to_str((uint64_t)trace_enabled, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0;
        goto out;
    }
    /* l — list hide paths */
    if (args[0]=='l' && (args[1] == 0 || args[1] == '\n')) {
        char *buf = g_outbuf; int n = 0;
        const char *m="L:"; while(*m)buf[n++]=*m++;
        n += u64_to_str((uint64_t)hide_paths_count, buf+n);
        buf[n++]='\n';
        while (__sync_lock_test_and_set(&hide_lock, 1)) ;
        for (int i = 0; i < hide_paths_count && n + hide_paths_len[i] + 2 < OUTBUF_SZ; i++) {
            for (int j = 0; j < hide_paths_len[i]; j++) buf[n++] = hide_paths[i][j];
            buf[n++] = '\n';
        }
        __sync_lock_release(&hide_lock);
        buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
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
    pr_info("[fakemem-v20] init\n");
    task_pid_nr_ns_fn = (task_pid_nr_ns_t)kallsyms_lookup_name("__task_pid_nr_ns");
    copy_from_user_nofault_fn = (copy_from_user_nofault_t)kallsyms_lookup_name("copy_from_user_nofault");
    if (!copy_from_user_nofault_fn)
        copy_from_user_nofault_fn = (copy_from_user_nofault_t)kallsyms_lookup_name("__copy_from_user_inatomic");
    find_get_pid_fn = (find_get_pid_t)kallsyms_lookup_name("find_get_pid");
    put_pid_fn = (put_pid_t)kallsyms_lookup_name("put_pid");
    get_pid_task_fn = (get_pid_task_t)kallsyms_lookup_name("get_pid_task");
    access_process_vm_fn = (access_process_vm_t)kallsyms_lookup_name("access_process_vm");
    pr_info("[fakemem-v20] fns: pidns=%llx cfu=%llx access=%llx\n",
            (uint64_t)task_pid_nr_ns_fn, (uint64_t)copy_from_user_nofault_fn,
            (uint64_t)access_process_vm_fn);

    for (int i = 0; i < MAX_FAKE_FDS; i++) fake_fds[i].active = 0;
    hide_paths_count = 0;

    /* v17 hooks */
    hook_err_t e1 = inline_hook_syscalln(__NR_fchmodat, 3, before_fchmodat, 0, 0);
    hook_err_t e2 = inline_hook_syscalln(__NR_openat, 4, before_openat_hide, after_openat, 0);
    hook_err_t e3 = inline_hook_syscalln(__NR_read, 3, 0, after_read, 0);
    hook_err_t e4 = inline_hook_syscalln(__NR_close, 1, before_close, 0, 0);
    /* v18 new hooks */
    hook_err_t e5 = inline_hook_syscalln(__NR_faccessat, 3, before_faccessat, 0, 0);
    hook_err_t e6 = inline_hook_syscalln(__NR_faccessat2, 4, before_faccessat2, 0, 0);
    hook_err_t e7 = inline_hook_syscalln(__NR3264_fstatat, 4, before_newfstatat, 0, 0);
    hook_err_t e8 = inline_hook_syscalln(__NR_statx, 5, before_statx, 0, 0);
    pr_info("[fakemem-v20] hooks: fchmodat=%d openat=%d read=%d close=%d faccessat=%d faccessat2=%d newfstatat=%d statx=%d\n",
            e1, e2, e3, e4, e5, e6, e7, e8);
    return 0;
}

static long sgs_exit(void *__user reserved)
{
    inline_unhook_syscalln(__NR_fchmodat, before_fchmodat, 0);
    inline_unhook_syscalln(__NR_openat, before_openat_hide, after_openat);
    inline_unhook_syscalln(__NR_read, 0, after_read);
    inline_unhook_syscalln(__NR_close, before_close, 0);
    inline_unhook_syscalln(__NR_faccessat, before_faccessat, 0);
    inline_unhook_syscalln(__NR_faccessat2, before_faccessat2, 0);
    inline_unhook_syscalln(__NR3264_fstatat, before_newfstatat, 0);
    inline_unhook_syscalln(__NR_statx, before_statx, 0);
    pr_info("[fakemem-v20] exit reads=%llu lines_removed=%llu hide_access=%llu hide_stat=%llu hide_open=%llu\n",
            total_reads, fake_lines_removed,
            hide_blocks_access, hide_blocks_stat, hide_blocks_open);
    return 0;
}

KPM_INIT(sgs_init);
KPM_CTL0(sgs_ctl0);
KPM_EXIT(sgs_exit);
