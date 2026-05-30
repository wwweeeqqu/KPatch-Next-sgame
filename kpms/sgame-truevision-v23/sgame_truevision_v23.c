/* SPDX-License-Identifier: GPL-2.0-or-later */
/* sgame-truevision v23 — v20-mem (fake-maps + hide + cross-proc read)
 *                        + ARM64 HW execution breakpoint PROBE.
 *
 * 承接 (memory): sgame-hwbp-plan-2026-05-29 / sgame-hwbp-buildfacts-2026-05-29 /
 *   sgame-sim-position-store-2026-05-29. 纯读路对真深雾全死, 转 HW BP 当探针:
 *   钉权威坐标 setter sub_03c511a0 (libGameCore RVA 0x03c511a0, x0=c=ActorNode,
 *   x1=ptr->VInt3 12B 雾前权威), 露头时抓 {c, VInt3} -> reader 按位置关联 c->objID ->
 *   摘断点退纯读 c+0x60 (transient) 或常驻抓写 (persistent, 视 D4 实测).
 *
 * HW BP 机制照搬本仓库已编译跑通的 kpms/sgame-sniff/sgame_sniff.c (perf_attr_v61
 *   布局 + register_user_hw_breakpoint), 但修正了它的 task-ref bug (见 tv_put_task):
 *   sniff 在 register 后直接 raw __put_task_struct(tsk) = UAF (perf 自己持 ref);
 *   本版保留 ref 到 tvoff, 用 refcount-dec-and-test + 条件 __put; 偏移未知时故意泄漏
 *   (安全, 不崩), D2 经 tvcfg 设 usage_off 后才启用正确释放.
 *
 * 反检测 PASS ~0.82 (libtersafe 零 HW debug-reg 自检; perf BP != ptrace 无冲突).
 *
 * ctl commands (v20 原有全部保留, reader 'r'/'rf' 读路不变):
 *   s / p <tgid> / c / r <pid> <addr> <len> / rf .. / h <path> / H / l / L / D / T
 *   --- v23 新增 HW BP 探针 verbs ---
 *   tvon <bp_hex_va> <tid1> <tid2> ...  — arm exec BP on setter VA for listed tids
 *   tvget                               — dump {c -> VInt3} capture table
 *   tvoff                               — unregister all BPs + clear tables
 *   tvcfg usageoff=<dec>                — set task_struct->usage offset (enable proper task-ref put)
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

KPM_NAME("sgame-truevision-v23");
KPM_VERSION("0.23.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("ctf");
KPM_DESCRIPTION("v20 fakemem/hide/read + ARM64 HW-BP probe (setter sub_03c511a0 -> {c,VInt3})");

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

/* ======================= v23 HW BREAKPOINT (probe) ======================= *
 * 照搬 kpms/sgame-sniff/sgame_sniff.c 的 perf HW-BP 机制 (已编译跑通), 修正其
 * task-ref bug. pt_regs 来自 <asm/ptrace.h> (已 include): regs[31] -> x0=regs[0].
 */
struct perf_event;
struct perf_sample_data;
/* struct pt_regs / struct task_struct / struct pid / enum pid_type 已在上方声明 */

typedef void (*perf_overflow_handler_t)(struct perf_event *, struct perf_sample_data *, struct pt_regs *);
typedef struct perf_event *(*reg_user_hwbp_t)(void *attr, perf_overflow_handler_t, void *ctx, struct task_struct *tsk);
typedef void (*unreg_hwbp_t)(struct perf_event *);
typedef void (*put_task_struct_t)(struct task_struct *);
typedef int  (*perf_event_enable_t)(struct perf_event *);   /* arm-disabled-then-enable fix */
typedef void (*perf_event_disable_t)(struct perf_event *);

static reg_user_hwbp_t reg_user_hwbp_fn = 0;
static unreg_hwbp_t unreg_hwbp_fn = 0;
static put_task_struct_t put_task_struct_fn = 0;  /* __put_task_struct (raw final-free) */
static perf_event_enable_t perf_event_enable_fn = 0;
static perf_event_disable_t perf_event_disable_fn = 0;

/* perf_event_attr — 与 sgame-sniff perf_attr_v61 字节布局一致 (mainline 6.1 UAPI):
 * bp_type@0x34, bp_addr@0x38, bp_len@0x40, size=0x80. 用裸 u64 flags.
 * ★ 2026-05-30 修法: flags=0x65 = disabled(bit0)=1 | pinned(bit2) | exclude_kernel(bit5) |
 *   exclude_hv(bit6). disabled=1 镜像已验证不卡的 RT 6.1.ko (我们旧 0x64=disabled=0 立即跨CPU
 *   IPI 安装 → step-over 竞争 → 无限重触发 RCU stall, 见 sgame-hwbp-armwedge-2026-05-30).
 *   arm 时不触发; 之后 tvenable 从非原子 ctl0 调 perf_event_enable 走正常 task-ctx 调度装硬件. */
struct tv_perf_attr {
    uint32_t type;        /* 0x00 = 5 (PERF_TYPE_BREAKPOINT) */
    uint32_t size;        /* 0x04 = 0x80 */
    uint64_t config;      /* 0x08 */
    uint64_t period;      /* 0x10 */
    uint64_t sample_type; /* 0x18 */
    uint64_t read_format; /* 0x20 */
    uint64_t flags;       /* 0x28 bitfield word */
    uint32_t wakeup;      /* 0x30 */
    uint32_t bp_type;     /* 0x34 = 4 (HW_BREAKPOINT_X) */
    uint64_t bp_addr;     /* 0x38 = setter VA */
    uint64_t bp_len;      /* 0x40 = 4 (HW_BREAKPOINT_LEN_4) */
    uint8_t  rest[0x80 - 0x48]; /* 0x48..0x7f reserved */
};

#define TV_FLAGS_DISARMED 0x65ULL  /* disabled|pinned|exclude_kernel|exclude_hv (arm OFF, enable later) */
#define TV_BP_EXEC  4   /* HW_BREAKPOINT_X */
#define TV_BP_WRITE 2   /* HW_BREAKPOINT_W (data watchpoint — wedge-immune) */

#define TV_MAX_BPS 256
struct tv_bp { int in_use; pid_t tid; struct perf_event *ev; struct task_struct *tsk; volatile uint64_t hits; };
static struct tv_bp g_bps[TV_MAX_BPS];

/* capture table keyed by c (ActorNode pointer). c==0 = empty slot (claim sentinel). */
#define TV_CAP_N 64
struct tv_cap { volatile uint64_t c; int32_t v[3]; uint32_t tid; volatile uint64_t hits; };
static struct tv_cap g_caps[TV_CAP_N];

static volatile uint64_t tv_total_hits = 0;   /* total BP fires processed */
static volatile uint64_t tv_cfu_fail = 0;     /* x1 deref faulted -> dropped */
static volatile uint64_t tv_bp_va = 0;        /* armed setter/data VA (status) */
static volatile uint64_t tv_first_fire_pc = 0;/* PC of the FIRST fire (reader detects firing fast) */
static volatile uint64_t tv_hit_cap = 500;    /* handler does heavy work only for first N fires (bound runaway) */
static volatile int      tv_armed = 0;        /* # perf_events currently registered */
static volatile int      tv_enabled = 0;      /* # perf_events enabled via tvenable */
static volatile int      g_usage_off = 0;     /* task_struct->usage offset; 0 = leak ref (safe), set via tvcfg after D2 */

/* SAFE task-ref release. perf holds its OWN ref after register; we drop ONLY ours.
 * usage_off==0 -> leak (do NOT raw __put_task_struct: that final-frees a live task = UAF).
 * usage_off>0 -> refcount_dec_and_test(&t->usage); 仅归 0 才 __put_task_struct. */
static void tv_put_task(struct task_struct *t)
{
    if (!t) return;
    if (g_usage_off <= 0) return;  /* safe leak until offset verified on-device */
    int *usage = (int *)((char *)t + g_usage_off);
    if (__sync_sub_and_fetch(usage, 1) == 0) {
        if (put_task_struct_fn) put_task_struct_fn(t);
    }
}

/* perf overflow handler — runs in ARM64 debug-exception/atomic context.
 * NO sleep, NO page-table walk, NO deref of unverified user ptr except via
 * copy_from_user_nofault (returns nonzero on fault, never sleeps). */
static void tv_bp_handler(struct perf_event *ev, struct perf_sample_data *sd, struct pt_regs *regs)
{
    if (!regs) return;
    /* count EVERY fire first (reader polls this to detect firing immediately + issue tvoff). */
    uint64_t n = __sync_fetch_and_add(&tv_total_hits, 1);
    if (tv_first_fire_pc == 0) tv_first_fire_pc = regs->pc;   /* sanity: where it fired */
    if (n >= tv_hit_cap) return;             /* safety neuter: bound handler work past cap */

    uint64_t c   = regs->regs[0];   /* x0 = c (ActorNode) — valid for EXEC BP at setter entry */
    uint64_t src = regs->regs[1];   /* x1 = ptr -> source VInt3 (12B) — EXEC BP only */
    if (!c || !src) return;
    if (src >= 0x800000000000ULL) return;   /* user-range guard */
    if (!copy_from_user_nofault_fn) return;
    int32_t v[3];
    if (copy_from_user_nofault_fn(v, (const void __user *)src, 12) != 0) {
        __sync_fetch_and_add(&tv_cfu_fail, 1);
        return;                              /* faulted -> DISCARD (iron law) */
    }

    /* attribute the fire to its bp slot (-> tid), pure pointer scan */
    pid_t tid = 0;
    for (int i = 0; i < TV_MAX_BPS; i++) {
        if (g_bps[i].in_use && g_bps[i].ev == ev) {
            __sync_fetch_and_add(&g_bps[i].hits, 1);
            tid = g_bps[i].tid;
            break;
        }
    }

    /* dedup-insert into g_caps keyed by c (lock-free per-slot CAS). */
    int free_slot = -1;
    for (int i = 0; i < TV_CAP_N; i++) {
        uint64_t cur = g_caps[i].c;
        if (cur == c) {
            g_caps[i].v[0] = v[0]; g_caps[i].v[1] = v[1]; g_caps[i].v[2] = v[2];
            g_caps[i].tid = tid;
            __sync_fetch_and_add(&g_caps[i].hits, 1);
            return;
        }
        if (cur == 0 && free_slot < 0) free_slot = i;
    }
    if (free_slot >= 0 && __sync_bool_compare_and_swap(&g_caps[free_slot].c, 0ULL, c)) {
        g_caps[free_slot].v[0] = v[0]; g_caps[free_slot].v[1] = v[1]; g_caps[free_slot].v[2] = v[2];
        g_caps[free_slot].tid = tid;
        __sync_fetch_and_add(&g_caps[free_slot].hits, 1);
    }
    /* table full (>64 distinct c) -> drop. ~10 entities => never full. */
}

static void tv_fill_attr(struct tv_perf_attr *a, uint64_t va, uint32_t bp_type, uint64_t bp_len)
{
    my_memset(a, 0, sizeof(*a));
    a->type    = 5;                 /* PERF_TYPE_BREAKPOINT */
    a->size    = (uint32_t)sizeof(*a); /* 0x80 */
    a->bp_type = bp_type;           /* 4=X exec / 2=W data watchpoint */
    a->bp_addr = va;                /* exec: 4-aligned code VA; watch: data VA */
    a->bp_len  = bp_len;            /* exec=4 (kernel req), watch=8 */
    a->flags   = TV_FLAGS_DISARMED; /* disabled=1: arm OFF, enable later via tvenable */
}

/* arm one per-task BP (disabled) on tid @ va. Keeps OUR task ref in the slot (released at tvoff).
 * bp_type: 4=exec(X) / 2=write-watchpoint(W). Event is created DISABLED; call tvenable to fire. */
static int tv_arm_one(pid_t tid, uint64_t va, uint32_t bp_type, uint64_t bp_len)
{
    if (!reg_user_hwbp_fn || !find_get_pid_fn || !get_pid_task_fn) return -1;
    if (va == 0 || va >= 0x800000000000ULL) return -2;
    if (bp_type == TV_BP_EXEC && (va & 3)) return -2;   /* exec must be 4-aligned */
    int slot = -1;
    for (int i = 0; i < TV_MAX_BPS; i++) if (!g_bps[i].in_use) { slot = i; break; }
    if (slot < 0) return -3;
    struct pid *pp = find_get_pid_fn(tid);
    if (!pp) return -4;
    struct task_struct *tsk = get_pid_task_fn(pp, PIDTYPE_PID);
    if (put_pid_fn) put_pid_fn(pp);
    if (!tsk) return -5;
    struct tv_perf_attr attr;
    tv_fill_attr(&attr, va, bp_type, bp_len);
    struct perf_event *ev = reg_user_hwbp_fn((void *)&attr, tv_bp_handler, 0, tsk);
    if (!ev || ((long)ev >= -4095L && (long)ev < 0)) {
        tv_put_task(tsk);           /* register failed -> drop our ref (safe) */
        return -6;
    }
    g_bps[slot].in_use = 1;
    g_bps[slot].tid = tid;
    g_bps[slot].ev = ev;
    g_bps[slot].tsk = tsk;          /* hold our ref; release at tvoff */
    g_bps[slot].hits = 0;
    __sync_fetch_and_add(&tv_armed, 1);
    return slot;
}

static void tv_disarm_all(void)
{
    for (int i = 0; i < TV_MAX_BPS; i++) {
        if (!g_bps[i].in_use) continue;
        if (perf_event_disable_fn && g_bps[i].ev) perf_event_disable_fn(g_bps[i].ev); /* stop firing first */
        if (unreg_hwbp_fn && g_bps[i].ev) unreg_hwbp_fn(g_bps[i].ev);  /* drops perf's ref */
        tv_put_task(g_bps[i].tsk);                                    /* then drop OUR ref */
        g_bps[i].in_use = 0; g_bps[i].ev = 0; g_bps[i].tsk = 0; g_bps[i].tid = 0; g_bps[i].hits = 0;
    }
    for (int i = 0; i < TV_CAP_N; i++) {
        g_caps[i].c = 0; g_caps[i].v[0] = g_caps[i].v[1] = g_caps[i].v[2] = 0;
        g_caps[i].tid = 0; g_caps[i].hits = 0;
    }
    tv_armed = 0; tv_enabled = 0; tv_total_hits = 0; tv_cfu_fail = 0;
    tv_bp_va = 0; tv_first_fire_pc = 0;
}

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
        buf[n++]=' ';
        p="tv_armed="; while(*p)buf[n++]=*p++; n += u64_to_str((uint64_t)tv_armed, buf+n); buf[n++]=' ';
        p="tv_enabled="; while(*p)buf[n++]=*p++; n += u64_to_str((uint64_t)tv_enabled, buf+n); buf[n++]=' ';
        p="tv_hits="; while(*p)buf[n++]=*p++; n += u64_to_str(tv_total_hits, buf+n); buf[n++]=' ';
        p="tv_fired="; while(*p)buf[n++]=*p++; n += u64_to_str((uint64_t)(tv_first_fire_pc!=0), buf+n); buf[n++]=' ';
        p="tv_cfu_fail="; while(*p)buf[n++]=*p++; n += u64_to_str(tv_cfu_fail, buf+n); buf[n++]=' ';
        p="tv_usageoff="; while(*p)buf[n++]=*p++; n += u64_to_str((uint64_t)(g_usage_off>0?g_usage_off:0), buf+n);
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
    /* 'r <pid> <addr> <len>' — cross-process mem-read (普通 GUP)
     * 'rf <pid> <addr> <len>' — same, but with FOLL_FORCE flag (bypass VMA PROT check)
     *   适合排位模式 sgame mprotect PROT_NONE 屏蔽 chain endpoint 的场景
     *   FOLL_FORCE 不能 bypass: zap_page_range / lazy alloc / munmap (PTE empty 时仍 fail) */
    if (args[0]=='r' && (args[1]==' ' || (args[1]=='f' && args[2]==' '))) {
        int use_force = (args[1]=='f');
        const char *p = args + (use_force ? 3 : 2);
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
        /* FOLL_FORCE = 0x10 (kernel 5.x/6.x typical, bypass PROT check in GUP) */
        unsigned int gup_flags = use_force ? 0x10 : 0;
        int r = access_process_vm_fn(tsk, (unsigned long)addr, rb, (int)len, gup_flags);
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
    /* ===== v23 HW BP probe verbs ===== */
    /* tvon <bp_hex_va> <tid1> <tid2> ... — arm exec BP on VA for each tid (appends). */
    if (args[0]=='t' && args[1]=='v' && args[2]=='o' && args[3]=='n') {
        const char *p = args + 4;
        uint64_t va = parse_hex(&p);
        if (va == 0) {
            const char *m="E:tvon_noaddr\n"; compat_copy_to_user(out_msg, m, 14); goto out;
        }
        if (tv_armed == 0) {  /* fresh session: clear capture table + counters */
            for (int i = 0; i < TV_CAP_N; i++) {
                g_caps[i].c = 0; g_caps[i].v[0]=g_caps[i].v[1]=g_caps[i].v[2]=0;
                g_caps[i].tid = 0; g_caps[i].hits = 0;
            }
            tv_total_hits = 0; tv_cfu_fail = 0;
        }
        tv_bp_va = va;
        int regd = 0, failed = 0;
        while (1) {
            while (*p == ' ') p++;
            if (*p < '0' || *p > '9') break;
            pid_t tid = parse_dec(&p);
            if (tid <= 0) continue;
            int rc2 = tv_arm_one(tid, va, TV_BP_EXEC, 4);   /* exec, DISABLED (tvenable to fire) */
            if (rc2 >= 0) regd++; else failed++;
        }
        char *buf = g_outbuf; int n = 0;
        const char *m = "TVON(exec,disabled): bp=0x"; while (*m) buf[n++] = *m++;
        { static const char hx[]="0123456789abcdef"; char hb[16]; int hi=0; uint64_t vv=va;
          if (!vv) hb[hi++]='0'; else while (vv) { hb[hi++]=hx[vv&0xf]; vv>>=4; }
          for (int j=hi-1;j>=0;j--) buf[n++]=hb[j]; }
        m=" regd="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)regd, buf+n);
        m=" failed="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)failed, buf+n);
        m=" armed="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)tv_armed, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
    }
    /* tvwon <data_hex_va> <tid1> <tid2> ... — arm WRITE WATCHPOINT (disabled) on data VA.
     * Watchpoint fires AFTER the store completes -> wedge-immune (safe probe). */
    if (args[0]=='t' && args[1]=='v' && args[2]=='w' && args[3]=='o' && args[4]=='n') {
        const char *p = args + 5;
        uint64_t va = parse_hex(&p);
        if (va == 0) { const char *m="E:tvwon_noaddr\n"; compat_copy_to_user(out_msg, m, 15); goto out; }
        if (tv_armed == 0) {
            for (int i = 0; i < TV_CAP_N; i++) { g_caps[i].c = 0; g_caps[i].hits = 0; g_caps[i].tid = 0; }
            tv_total_hits = 0; tv_cfu_fail = 0; tv_first_fire_pc = 0;
        }
        tv_bp_va = va;
        int regd = 0, failed = 0;
        while (1) {
            while (*p == ' ') p++;
            if (*p < '0' || *p > '9') break;
            pid_t tid = parse_dec(&p);
            if (tid <= 0) continue;
            int rc2 = tv_arm_one(tid, va, TV_BP_WRITE, 8);   /* write watchpoint, DISABLED */
            if (rc2 >= 0) regd++; else failed++;
        }
        char *buf = g_outbuf; int n = 0;
        const char *m = "TVWON(watch,disabled): d=0x"; while (*m) buf[n++]=*m++;
        { static const char hx[]="0123456789abcdef"; char hb[16]; int hi=0; uint64_t vv=va;
          if (!vv) hb[hi++]='0'; else while (vv) { hb[hi++]=hx[vv&0xf]; vv>>=4; }
          for (int j=hi-1;j>=0;j--) buf[n++]=hb[j]; }
        m=" regd="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)regd, buf+n);
        m=" failed="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)failed, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
    }
    /* tvenable — enable all armed (disabled) events via perf_event_enable (non-atomic ctl0 ctx).
     * THIS is the step that actually arms hardware + can fire. Have power button ready (exec). */
    if (args[0]=='t' && args[1]=='v' && args[2]=='e' && args[3]=='n' && args[4]=='a') {
        int en = 0;
        if (perf_event_enable_fn) {
            for (int i = 0; i < TV_MAX_BPS; i++) {
                if (g_bps[i].in_use && g_bps[i].ev) { perf_event_enable_fn(g_bps[i].ev); en++; }
            }
        }
        tv_enabled = en;
        char *buf = g_outbuf; int n = 0;
        const char *m;
        if (!perf_event_enable_fn) { m = "E:no_perf_event_enable\n"; while (*m) buf[n++]=*m++; }
        else { m = "TVENABLE: enabled="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)en, buf+n); }
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
    }
    /* tvget — dump {c -> VInt3} table (slots with hits>=2). */
    if (args[0]=='t' && args[1]=='v' && args[2]=='g' && args[3]=='e' && args[4]=='t') {
        static const char hx[] = "0123456789abcdef";
        char *buf = g_outbuf; int n = 0;
        int cnt = 0;
        for (int i = 0; i < TV_CAP_N; i++) if (g_caps[i].c != 0 && g_caps[i].hits >= 2) cnt++;
        const char *m = "TVGET: n="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)cnt, buf+n);
        m=" hits="; while (*m) buf[n++]=*m++; n += u64_to_str(tv_total_hits, buf+n);
        m=" cfu_fail="; while (*m) buf[n++]=*m++; n += u64_to_str(tv_cfu_fail, buf+n);
        buf[n++]='\n';
        for (int i = 0; i < TV_CAP_N; i++) {
            if (g_caps[i].c == 0 || g_caps[i].hits < 2) continue;
            if (n > OUTBUF_SZ - 96) break;  /* keep room */
            buf[n++]='0'; buf[n++]='x';
            { char hb[16]; int hi=0; uint64_t vv=g_caps[i].c;
              if (!vv) hb[hi++]='0'; else while (vv) { hb[hi++]=hx[vv&0xf]; vv>>=4; }
              for (int j=hi-1;j>=0;j--) buf[n++]=hb[j]; }
            for (int k = 0; k < 3; k++) {
                buf[n++]=' ';
                int32_t sv = g_caps[i].v[k];
                uint64_t uv;
                if (sv < 0) { buf[n++]='-'; uv = (uint64_t)(-(int64_t)sv); }
                else uv = (uint64_t)sv;
                n += u64_to_str(uv, buf+n);
            }
            m=" tid="; while (*m) buf[n++]=*m++; n += u64_to_str((uint64_t)g_caps[i].tid, buf+n);
            m=" hits="; while (*m) buf[n++]=*m++; n += u64_to_str(g_caps[i].hits, buf+n);
            buf[n++]='\n';
        }
        buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
    }
    /* tvoff — unregister all BPs + clear tables. */
    if (args[0]=='t' && args[1]=='v' && args[2]=='o' && args[3]=='f' && args[4]=='f') {
        int was = tv_armed;
        tv_disarm_all();
        char *buf = g_outbuf; int n = 0;
        const char *m = "TVOFF: unregd="; while (*m) buf[n++]=*m++;
        n += u64_to_str((uint64_t)was, buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
    }
    /* tvcfg usageoff=<dec> — set task_struct->usage offset (enable proper task-ref put). */
    if (args[0]=='t' && args[1]=='v' && args[2]=='c' && args[3]=='f' && args[4]=='g') {
        const char *p = args + 5;
        /* find "usageoff=" */
        const char *key = "usageoff=";
        const char *q = 0;
        for (int i = 0; p[i]; i++) {
            int j; for (j = 0; key[j]; j++) if (p[i+j] != key[j]) break;
            if (key[j] == 0) { q = p + i + j; break; }
        }
        if (q) { g_usage_off = (int)parse_dec(&q); }
        char *buf = g_outbuf; int n = 0;
        const char *m = "TVCFG: usage_off="; while (*m) buf[n++]=*m++;
        n += u64_to_str((uint64_t)(g_usage_off > 0 ? g_usage_off : 0), buf+n);
        buf[n++]='\n'; buf[n]=0;
        compat_copy_to_user(out_msg, buf, n+1);
        rc = 0; goto out;
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
    pr_info("[truevision-v23] fns: pidns=%llx cfu=%llx access=%llx fgpid=%llx gpt=%llx\n",
            (uint64_t)task_pid_nr_ns_fn, (uint64_t)copy_from_user_nofault_fn,
            (uint64_t)access_process_vm_fn, (uint64_t)find_get_pid_fn, (uint64_t)get_pid_task_fn);

    /* v23 HW BP symbols */
    reg_user_hwbp_fn = (reg_user_hwbp_t)kallsyms_lookup_name("register_user_hw_breakpoint");
    unreg_hwbp_fn = (unreg_hwbp_t)kallsyms_lookup_name("unregister_hw_breakpoint");
    put_task_struct_fn = (put_task_struct_t)kallsyms_lookup_name("__put_task_struct");
    perf_event_enable_fn = (perf_event_enable_t)kallsyms_lookup_name("perf_event_enable");
    perf_event_disable_fn = (perf_event_disable_t)kallsyms_lookup_name("perf_event_disable");
    pr_info("[truevision-v23] hwbp: reg=%llx unreg=%llx put_task=%llx (usage_off=%d 0=leak-safe)\n",
            (uint64_t)reg_user_hwbp_fn, (uint64_t)unreg_hwbp_fn,
            (uint64_t)put_task_struct_fn, g_usage_off);
    pr_info("[truevision-v23] hwbp: perf_enable=%llx perf_disable=%llx (0=>tvenable dead, use watchpoint or pivot)\n",
            (uint64_t)perf_event_enable_fn, (uint64_t)perf_event_disable_fn);

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
    tv_disarm_all();   /* v23: unregister all HW BPs + release task refs first */
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
