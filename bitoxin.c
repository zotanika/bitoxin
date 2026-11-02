// SPDX-License-Identifier: GPL-2.0-or-later
/* BITOXIN 2: a preemptible state-integrity probe alongside external QA scenarios. */
#define BITOXIN_PROBES   /* declare bitoxin_probe_point() for W=1 */
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/kthread.h>
#include <linux/freezer.h>
#include <linux/delay.h>
#include <linux/vmalloc.h>
#include <linux/slab.h>
#include <linux/debugfs.h>
#include <linux/seq_file.h>
#include <linux/mutex.h>
#include <linux/suspend.h>
#include <linux/ktime.h>
#include <linux/cpu.h>
#include <linux/cpumask.h>
#include <linux/sched.h>
#include <linux/sched/task.h>
#include <linux/percpu.h>
#include <linux/rcupdate.h>
#include <linux/string.h>
#include <linux/kdebug.h>
#include <linux/uaccess.h>
#include <linux/ptrace.h>
#include "bitoxin_core.h"
#include "bitoxin_hook.h"

#define BX_MAX_WORKERS 32
/* Large probe buffers must fail, not wake the OOM killer, when memory is short. */
#define BX_GFP (GFP_KERNEL | __GFP_NOWARN | __GFP_NORETRY)
static unsigned int threads = 1, mem_kib = 1024, seed = 1, chunk = 4096, pause_ms;
static unsigned int lane_rounds = 1, hook_budget = 4096;
static unsigned long long passes;
static bool freezable, panic_on_error, trap, churn, per_cpu;
module_param(threads, uint, 0444);
MODULE_PARM_DESC(threads, "Workers (0..32; 0 = hook only); ignored with per_cpu");
module_param(mem_kib, uint, 0444);
MODULE_PARM_DESC(mem_kib, "Power-of-two KiB per worker, 0 = largest that allocates; total <=256 MiB");
module_param(seed, uint, 0444);
MODULE_PARM_DESC(seed, "Nonzero first-worker seed, smaller than buffer bit count");
module_param(chunk, uint, 0444);
MODULE_PARM_DESC(chunk, "Operations between stop/freezer/status checks (1..65536); a chunk has no scheduling point, so chunk * lane_rounds <= 16777216");
module_param(pause_ms, uint, 0444);
MODULE_PARM_DESC(pause_ms, "Optional interruptible pause per chunk (0..1000 ms)");
module_param(passes, ullong, 0444);
MODULE_PARM_DESC(passes, "Verified directional passes per worker; zero runs until unload/error");
module_param(freezable, bool, 0444);
MODULE_PARM_DESC(freezable, "Cooperate with the suspend freezer (default false: run through transitions)");
module_param(panic_on_error, bool, 0444);
MODULE_PARM_DESC(panic_on_error, "Panic after logging the first probe failure (default false)");
module_param(trap, bool, 0444);
MODULE_PARM_DESC(trap, "Trap in place (brk/ebreak) on any failure with chain registers live");
module_param(lane_rounds, uint, 0444);
MODULE_PARM_DESC(lane_rounds, "Register-chain repetitions per operation (1..65536); chunk * lane_rounds <= 16777216, hook_budget * lane_rounds <= 65536");
module_param(churn, bool, 0444);
MODULE_PARM_DESC(churn, "Replace each worker buffer with a fresh vmalloc at verified pass boundaries; the next buffer is allocated before the old is freed, so with mem_kib=0 most churns may fail (counted; no OOM kill)");
module_param(per_cpu, bool, 0444);
MODULE_PARM_DESC(per_cpu, "One worker per online CPU, re-pinned to its home CPU after hotplug");
module_param(hook_budget, uint, 0444);
MODULE_PARM_DESC(hook_budget, "Operations per bitoxin_probe_point() call (1..65536); the call runs with preemption disabled, so hook_budget * lane_rounds <= 65536");

struct bx_snapshot {
    u64 passes, operations, audits, boottime_ns, cpu_changes, churns, churn_failures;
    u32 seed, walked, verified;
    int home_cpu, cpu;
    enum bx_phase phase;
    struct bx_error error;
    const char *state;
};
struct bx_worker {
    struct task_struct *task;
    struct bx_probe probe;
    u8 *buffer;
    u8 *pending;            /* churn: the next buffer while bx_rebind() runs */
    size_t size;
    unsigned int id;
    int home_cpu, cpu, seen_resume;
    u64 cpu_changes, churns, churn_failures;
    atomic_t trapped;       /* set by the die notifier (trap mode) */
    struct mutex snapshot_lock;
    struct bx_snapshot snapshot;
};
static struct bx_worker *workers;
static unsigned int nworkers, effective_kib;
static int homes[BX_MAX_WORKERS];
static struct dentry *debug_root;
static atomic_t abort_run = ATOMIC_INIT(0), resume_gen = ATOMIC_INIT(0);
static atomic64_t pm_prepare = ATOMIC64_INIT(0), pm_post = ATOMIC64_INIT(0);

/* Called outside the probe: readers never race the mutable probe cursor. */
static void publish(struct bx_worker *w, const char *state)
{
    struct bx_probe *p = &w->probe;
    mutex_lock(&w->snapshot_lock);
    w->snapshot = (struct bx_snapshot) {
        .passes = p->passes, .operations = p->operations, .audits = p->audits,
        .boottime_ns = ktime_get_boottime_ns(), .cpu_changes = w->cpu_changes,
        .churns = w->churns, .churn_failures = w->churn_failures, .seed = p->seed,
        .walked = p->walked, .verified = p->verified, .home_cpu = w->home_cpu,
        .cpu = w->cpu, .phase = p->phase, .error = p->error, .state = state,
    };
    mutex_unlock(&w->snapshot_lock);
}

static void report(const char *who, unsigned int id, const struct bx_probe *p)
{
    const struct bx_error *e = &p->error;
    pr_err("bitoxin: failure %s=%u seed=%u pass=%llu phase=%s bit=%u type=%s expected=%016llx observed=%016llx lane_reg=%s lane_expected=%016llx lane_observed=%016llx boottime_ns=%llu\n",
           who, id, p->seed, e->pass, e->phase == BX_WALK ? "walk" : "verify", e->bit,
           bx_result_name(e->code), e->expected, e->observed,
           bx_lane_reg_name(e->lane_index), e->lane_expected, e->lane_observed,
           ktime_get_boottime_ns());
    if (panic_on_error)
        panic("bitoxin: probe failure (see preceding record)");
}

static const char *fail_worker(struct bx_worker *w)
{
    publish(w, "failed");
    if (atomic_cmpxchg(&abort_run, 0, 1) == 0)
        report("worker", w->id, &w->probe);
    return "failed";
}

/* BSP hook: per-CPU retained state; each call continues that CPU's probe. */
#define BX_HOOK_BYTES 512U
struct bx_hook_cpu {
    struct bx_probe probe;
    u8 *buffer;            /* kmalloc: linear map, unlike the vmalloc workers */
    atomic_t busy;
    const char *site;
};
static DEFINE_PER_CPU(struct bx_hook_cpu, hook_cpu);
static DEFINE_PER_CPU(u64, hook_calls);
static DEFINE_PER_CPU(u64, hook_skips);
static bool hook_ready;   /* release/acquire: publishes every CPU's probe */
/* 0 none, 1 recording, 2 recorded (record mode), 3 trapped (cpu and site only) */
static atomic_t hook_failed = ATOMIC_INIT(0);
static struct { int cpu; char site[32]; struct bx_probe probe; } hook_failure;

static void hook_fail(struct bx_hook_cpu *h, const char *site)
{
    int cpu = smp_processor_id();
    if (atomic_cmpxchg(&hook_failed, 0, 1) == 0) {
        hook_failure.cpu = cpu;
        strscpy(hook_failure.site, site ? site : "?", sizeof(hook_failure.site));
        hook_failure.probe = h->probe;
        atomic_set_release(&hook_failed, 2);
    }
    if (atomic_cmpxchg(&abort_run, 0, 1) == 0) {
        pr_err("bitoxin: hook failure site=%s cpu=%d\n", site ? site : "?", cpu);
        report("hook_cpu", (unsigned int)cpu, &h->probe);
    }
}

void bitoxin_probe_point(const char *site)
{
    struct bx_hook_cpu *h = get_cpu_ptr(&hook_cpu);
    if (!smp_load_acquire(&hook_ready) || atomic_read(&abort_run) || !h->buffer)
        goto out;
    if (atomic_cmpxchg(&h->busy, 0, 1)) {   /* nested call on this CPU (IRQ) */
        this_cpu_inc(hook_skips);
        goto out;
    }
    this_cpu_inc(hook_calls);
    WRITE_ONCE(h->site, site);
    if (bx_run(&h->probe, hook_budget) != BX_OK)
        hook_fail(h, site);
    WRITE_ONCE(h->site, NULL);
    atomic_set(&h->busy, 0);
out:
    put_cpu_ptr(&hook_cpu);
}
EXPORT_SYMBOL_GPL(bitoxin_probe_point);

static int setup_hook(void)
{
    unsigned int cpu;
    for_each_possible_cpu(cpu) {
        struct bx_hook_cpu *h = per_cpu_ptr(&hook_cpu, cpu);
        h->buffer = kmalloc(BX_HOOK_BYTES, GFP_KERNEL);
        if (!h->buffer)
            return -ENOMEM;
        if (bx_init(&h->probe, h->buffer, BX_HOOK_BYTES, 1U + cpu % (BX_HOOK_BYTES * 8U - 1U)) != BX_OK ||
            bx_set_lane(&h->probe, lane_rounds, trap) != BX_OK)
            return -EINVAL;
    }
    smp_store_release(&hook_ready, true);
    return 0;
}

static void release_hook(void)
{
    unsigned int cpu;
    WRITE_ONCE(hook_ready, false);
    synchronize_rcu();   /* callers run with preemption disabled */
    for_each_possible_cpu(cpu) {
        kfree(per_cpu_ptr(&hook_cpu, cpu)->buffer);
        per_cpu_ptr(&hook_cpu, cpu)->buffer = NULL;
    }
}

/* Trap mode: the probe traps before it can record, so the die notifier latches
 * the failure (workers stop, the hook goes quiet), marks the trapping worker or
 * hook for the status file, and prints one decoded BITOXIN_TRAP line. */
static atomic_t trap_reported = ATOMIC_INIT(0);
static bool die_registered;

static unsigned long reg_at(struct pt_regs *regs, int n)
{
#if defined(__aarch64__)
    return n >= 0 && n < 31 ? regs->regs[n] : 0;
#elif defined(__riscv)
    return n > 0 && n < 32 ? ((unsigned long *)regs)[n] : 0; /* slot n is x<n> */
#else
    (void)regs; (void)n;
    return 0;
#endif
}

/* brk #0xb17 / ebreak followed by the marker word: our trap, not BUG(). The
 * marker is read only after the instruction matched, and never by a direct
 * load (on RISC-V it may be only 2-byte aligned). */
static bool is_bitoxin_trap(unsigned long pc)
{
    u32 insn = 0, marker = 0, expect = 0;
#if defined(__aarch64__)
    expect = 0xd4200000U | (0xb17U << 5);
#elif defined(__riscv)
    expect = 0x00100073U;
#endif
    if (!expect || copy_from_kernel_nofault(&insn, (const void *)pc, sizeof(insn)) ||
        insn != expect ||
        copy_from_kernel_nofault(&marker, (const void *)(pc + 4), sizeof(marker)))
        return false;
    return marker == BX_TRAP_MARKER;
}

/* Lane traps (kinds 1, 2): A = token, C = check word, bit = the visited bit.
 * C-detected traps (kinds 3, 4): A = expected, B = observed, C = bit. The
 * kernel has no FP/SIMD lane (kind 5). */
static int bx_die(struct notifier_block *nb, unsigned long val, void *data)
{
    static const char *const kinds[] = { "none", "register", "memory", "data", "state" };
    struct die_args *args = data;
    struct pt_regs *regs = args ? args->regs : NULL;
    struct bx_hook_cpu *h;
    const struct bx_probe *p = NULL;
    const char *site;
    char who[64] = "unknown";
    u64 kind, a, b, c, chain[BX_LANE_MAX], expected = 0, observed = 0;
    unsigned int i;
    int index = -1, cpu = raw_smp_processor_id();
    (void)nb; (void)val;
    if (!regs || !is_bitoxin_trap(instruction_pointer(regs)))
        return NOTIFY_DONE;
    atomic_set(&abort_run, 1);   /* the first failure latches globally */
    h = raw_cpu_ptr(&hook_cpu);
    site = READ_ONCE(h->site);
    if (atomic_read(&h->busy) && site) {
        snprintf(who, sizeof(who), "hook site=%s", site);
        p = &h->probe;
        if (atomic_cmpxchg(&hook_failed, 0, 1) == 0) {
            hook_failure.cpu = cpu;
            strscpy(hook_failure.site, site, sizeof(hook_failure.site));
            atomic_set_release(&hook_failed, 3);
        }
    } else {
        for (i = 0; workers && i < nworkers; ++i)
            if (workers[i].task == current) {
                snprintf(who, sizeof(who), "worker=%u", i);
                p = &workers[i].probe;
                atomic_set(&workers[i].trapped, 1);
            }
    }
    /* One record; RISC-V KGDB builds also notify DIE_TRAP before DIE_OOPS. */
    if (atomic_xchg(&trap_reported, 1))
        return NOTIFY_DONE;
    kind = reg_at(regs, bx_trap_regno(BX_TRAP_REG_KIND));
    a = reg_at(regs, bx_trap_regno(BX_TRAP_REG_A));
    b = reg_at(regs, bx_trap_regno(BX_TRAP_REG_B));
    c = reg_at(regs, bx_trap_regno(BX_TRAP_REG_C));
    if (kind == BX_LANE_REGISTER) {
        for (i = 0; i < (unsigned int)bx_lane_count(); ++i)
            chain[i] = reg_at(regs, bx_lane_regno((int)i));
        index = bx_lane_decode(a, chain, &expected, &observed);
    }
    pr_emerg("BITOXIN_TRAP kind=%s %s cpu=%d pass=%llu bit=%u a=%016llx b=%016llx c=%016llx lane_reg=%s lane_expected=%016llx lane_observed=%016llx\n",
             kind < ARRAY_SIZE(kinds) ? kinds[kind] : "unknown", who, cpu,
             p ? p->passes : 0,
             kind == BX_LANE_DATA || kind == BX_LANE_STATE ? (u32)c : (p ? p->cursor : 0),
             a, b, c, bx_lane_reg_name(index), expected, observed);
    return NOTIFY_DONE;
}
static struct notifier_block die_notifier = { .notifier_call = bx_die };

/* Last in teardown: a worker can trap until release_workers() has stopped it,
 * and bx_die() reads workers[] only for a trap of ours. */
static void release_die(void)
{
    if (die_registered) {
        unregister_die_notifier(&die_notifier);
        die_registered = false;
    }
}

/* Fresh vmalloc pages at a verified pass boundary; the next buffer is allocated
 * before the old one is released. A failed allocation or a refused rebind keeps
 * the old buffer and counts a churn failure. Corruption the rebind finds (the
 * released buffer changed since its verify, or the probe state is corrupt) is
 * latched in the probe and returned: the caller fails the worker. */
static int churn_buffer(struct bx_worker *w)
{
    u8 *next = __vmalloc(w->size, BX_GFP);
    int err;
    if (!next) {
        ++w->churn_failures;
        return BX_OK;
    }
    /* In trap mode corruption found by bx_rebind() oopses there instead of
     * returning; release_workers() then frees the pending buffer. */
    WRITE_ONCE(w->pending, next);
    err = bx_rebind(&w->probe, next);
    WRITE_ONCE(w->pending, NULL);
    if (err != BX_OK) {
        vfree(next);
        if (w->probe.error.code != BX_OK)
            return w->probe.error.code;
        ++w->churn_failures;
        return BX_OK;
    }
    vfree(w->buffer);
    w->buffer = next;
    ++w->churns;
    return BX_OK;
}

/* Count migrations; a per-CPU worker returns home once its CPU is active again. */
static void track_cpu(struct bx_worker *w)
{
    int cpu = raw_smp_processor_id();
    if (w->cpu >= 0 && cpu != w->cpu)
        ++w->cpu_changes;
    w->cpu = cpu;
    if (per_cpu && cpu != w->home_cpu && cpu_active(w->home_cpu)) {
        set_cpus_allowed_ptr(current, cpumask_of(w->home_cpu));
        cpu = raw_smp_processor_id();
        if (cpu != w->cpu) { ++w->cpu_changes; w->cpu = cpu; }
    }
}

static int probe_worker(void *arg)
{
    struct bx_worker *w = arg;
    const char *state = "stopped";
    if (freezable)
        set_freezable();
    w->seen_resume = atomic_read(&resume_gen);
    track_cpu(w);
    publish(w, "running");
    while (!kthread_should_stop() && !atomic_read(&abort_run)) {
        bool frozen = false;
        u64 before = w->probe.passes;
        int gen;
        if (passes && w->probe.passes >= passes) {
            state = "complete";
            break;
        }
        /* kthread_freezable_should_stop also avoids freezer/kthread_stop deadlocks.
         * State is not reinitialized when this call returns after resume. */
        if (freezable && kthread_freezable_should_stop(&frozen))
            break;
        gen = atomic_read(&resume_gen);
        if (frozen || gen != w->seen_resume) {   /* audit retained state after thaw */
            w->seen_resume = gen;
            if (bx_audit(&w->probe) != BX_OK) { state = fail_worker(w); break; }
        }
        if (atomic_read(&abort_run))
            break;
        if (bx_run(&w->probe, chunk) != BX_OK) { state = fail_worker(w); break; }
        if (churn && w->probe.passes != before && (!passes || w->probe.passes < passes) &&
            churn_buffer(w) != BX_OK) {
            state = fail_worker(w);
            break;
        }
        track_cpu(w);
        publish(w, "running");
        cond_resched();
        if (pause_ms)
            msleep_interruptible(pause_ms);
    }
    if (atomic_read(&abort_run) && w->probe.error.code == BX_OK)
        state = "aborted";
    publish(w, state);
    pr_info("bitoxin: worker=%u state=%s passes=%llu operations=%llu audits=%llu churns=%llu cpu_changes=%llu\n",
            w->id, state, w->probe.passes, w->probe.operations, w->probe.audits,
            w->churns, w->cpu_changes);
    /* Keep task_struct alive until module exit calls kthread_stop(). */
    while (!kthread_should_stop()) {
        if (freezable && kthread_freezable_should_stop(NULL))
            break;
        msleep_interruptible(100);
    }
    return 0;
}

static int pm_event(struct notifier_block *nb, unsigned long event, void *unused)
{
    (void)nb; (void)unused;
    if (event == PM_SUSPEND_PREPARE || event == PM_HIBERNATION_PREPARE) {
        atomic64_inc(&pm_prepare);
    } else if (event == PM_POST_SUSPEND || event == PM_POST_HIBERNATION) {
        atomic64_inc(&pm_post);
        atomic_inc(&resume_gen);   /* every worker audits at its next chunk */
    }
    return NOTIFY_OK;
}
static struct notifier_block pm_notifier = { .notifier_call = pm_event };

static const char *yes(bool v)
{
    return v ? "true" : "false";
}

static int status_show(struct seq_file *s, void *unused)
{
    unsigned int i;
    (void)unused;
    seq_printf(s, "{\"schema\":2,\"backend\":\"%s\",\"failed\":%s,\"mem_kib\":%u,\"requested_passes\":%llu,\"chunk\":%u,\"pause_ms\":%u,\"freezable\":%s,\"trap\":%s,\"lane_rounds\":%u,\"churn\":%s,\"per_cpu\":%s,\"pm_prepare\":%lld,\"pm_post\":%lld,\"workers\":[",
               bx_backend_name(), yes(atomic_read(&abort_run)), effective_kib, passes,
               chunk, pause_ms, yes(freezable), yes(trap), lane_rounds, yes(churn),
               yes(per_cpu), atomic64_read(&pm_prepare), atomic64_read(&pm_post));
    for (i = 0; i < nworkers; ++i) {
        struct bx_snapshot snap;
        mutex_lock(&workers[i].snapshot_lock);
        snap = workers[i].snapshot;
        mutex_unlock(&workers[i].snapshot_lock);
        if (atomic_read(&workers[i].trapped))
            snap.state = "trapped";
        seq_printf(s, "%s{\"id\":%u,\"state\":\"%s\",\"seed\":%u,\"home_cpu\":%d,\"cpu\":%d,\"cpu_changes\":%llu,\"churns\":%llu,\"churn_failures\":%llu,\"audits\":%llu,\"passes\":%llu,\"operations\":%llu,\"phase\":\"%s\",\"walked\":%u,\"verified\":%u,\"boottime_ns\":%llu,\"error\":\"%s\",\"error_bit\":%u,\"expected\":\"%016llx\",\"observed\":\"%016llx\",\"lane_reg\":\"%s\",\"lane_expected\":\"%016llx\",\"lane_observed\":\"%016llx\"}",
                   i ? "," : "", i, snap.state, snap.seed, snap.home_cpu, snap.cpu,
                   snap.cpu_changes, snap.churns, snap.churn_failures, snap.audits,
                   snap.passes, snap.operations, snap.phase == BX_WALK ? "walk" : "verify",
                   snap.walked, snap.verified, snap.boottime_ns,
                   bx_result_name(snap.error.code), snap.error.bit, snap.error.expected,
                   snap.error.observed, bx_lane_reg_name(snap.error.lane_index),
                   snap.error.lane_expected, snap.error.lane_observed);
    }
    seq_puts(s, "]");
    {
        u64 calls = 0, skips = 0;
        unsigned int cpu;
        int failed = atomic_read_acquire(&hook_failed);
        for_each_possible_cpu(cpu) {
            calls += per_cpu(hook_calls, cpu);
            skips += per_cpu(hook_skips, cpu);
        }
        seq_printf(s, ",\"hook\":{\"budget\":%u,\"calls\":%llu,\"nested_skips\":%llu,\"failed\":%s",
                   hook_budget, calls, skips, yes(failed));
        if (failed == 2) {
            const struct bx_probe *p = &hook_failure.probe;
            seq_printf(s, ",\"cpu\":%d,\"site\":\"%s\",\"error\":\"%s\",\"error_bit\":%u,\"expected\":\"%016llx\",\"observed\":\"%016llx\",\"lane_reg\":\"%s\",\"lane_expected\":\"%016llx\",\"lane_observed\":\"%016llx\"",
                       hook_failure.cpu, hook_failure.site, bx_result_name(p->error.code),
                       p->error.bit, p->error.expected, p->error.observed,
                       bx_lane_reg_name(p->error.lane_index), p->error.lane_expected,
                       p->error.lane_observed);
        } else if (failed == 3) {
            seq_printf(s, ",\"trapped\":true,\"cpu\":%d,\"site\":\"%s\"",
                       hook_failure.cpu, hook_failure.site);
        }
        seq_puts(s, "}");
    }
    seq_puts(s, "}\n");
    return 0;
}
static int status_open(struct inode *inode, struct file *file)
{
    return single_open(file, status_show, inode->i_private);
}
static const struct file_operations status_fops = {
    .owner = THIS_MODULE, .open = status_open, .read = seq_read,
    .llseek = seq_lseek, .release = single_release,
};

/* Largest power-of-two KiB per worker within 256 MiB total (mem_kib=0), halving
 * on allocation failure as the 2018 flowchart fell back to a lower degree. */
static int allocate_buffers(void)
{
    unsigned int kib = mem_kib, i;
    if (!nworkers) {   /* hook only */
        effective_kib = 0;
        return 0;
    }
    if (!kib) {
        kib = BX_MAX_BYTES / 1024;
        while ((u64)kib * nworkers > 256U * 1024U)
            kib >>= 1;
    }
    for (;;) {
        for (i = 0; i < nworkers; ++i) {
            workers[i].size = (size_t)kib * 1024U;
            workers[i].buffer = __vmalloc(workers[i].size, BX_GFP);
            if (!workers[i].buffer)
                break;
        }
        if (i == nworkers) {
            effective_kib = kib;
            return 0;
        }
        while (i--) {
            vfree(workers[i].buffer);
            workers[i].buffer = NULL;
        }
        if (mem_kib || kib == 1)
            return -ENOMEM;
        kib >>= 1;
    }
}

static void release_workers(void)
{
    unsigned int i;
    if (!workers)
        return;
    for (i = 0; i < nworkers; ++i)
        if (workers[i].task) {
            kthread_stop(workers[i].task);      /* also valid after a worker oops */
            put_task_struct(workers[i].task);
        }
    for (i = 0; i < nworkers; ++i) {
        vfree(workers[i].buffer);
        vfree(workers[i].pending);   /* left by an oops inside bx_rebind() */
    }
    kfree(workers);
    workers = NULL;
}

static int __init bitoxin_init(void)
{
    unsigned int i, cpu;
    int err;
    struct dentry *status;
    /* A chunk has no scheduling point and both target kernels are
     * PREEMPT_VOLUNTARY; a hook call runs with preemption disabled. The last
     * two tests bound their lane work (soft lockups, scheduling latency). */
    if ((!per_cpu && threads > BX_MAX_WORKERS) || mem_kib > BX_MAX_BYTES / 1024 ||
        (mem_kib & (mem_kib - 1)) || !seed || (mem_kib && seed >= mem_kib * 8192U) ||
        !chunk || chunk > 65536 || pause_ms > 1000 || !lane_rounds ||
        lane_rounds > BX_MAX_ROUNDS || !hook_budget || hook_budget > 65536 ||
        (u64)chunk * lane_rounds > (1U << 24) || (u64)hook_budget * lane_rounds > (1U << 16))
        return -EINVAL;
    nworkers = threads;
    if (per_cpu) {
        nworkers = 0;
        cpus_read_lock();
        for_each_online_cpu(cpu)
            if (nworkers < BX_MAX_WORKERS)
                homes[nworkers++] = (int)cpu;
        cpus_read_unlock();
    }
    if ((u64)mem_kib * nworkers > 256U * 1024U)
        return -EINVAL;
    workers = kcalloc(nworkers ? nworkers : 1, sizeof(*workers), GFP_KERNEL);
    if (!workers)
        return -ENOMEM;
    err = allocate_buffers();
    if (err)
        goto fail;
    if (nworkers && seed >= effective_kib * 8192U) {
        err = -EINVAL;
        goto fail;
    }
    for (i = 0; i < nworkers; ++i) {
        struct bx_worker *w = &workers[i];
        u32 worker_seed = 1U + ((seed - 1U + i) % (effective_kib * 8192U - 1U));
        w->id = i;
        w->home_cpu = per_cpu ? homes[i] : -1;
        w->cpu = -1;
        mutex_init(&w->snapshot_lock);
        if (bx_init(&w->probe, w->buffer, effective_kib * 1024U, worker_seed) != BX_OK ||
            bx_set_lane(&w->probe, lane_rounds, trap) != BX_OK) {
            err = -EINVAL;
            goto fail;
        }
        publish(w, "ready");
    }
    err = setup_hook();
    if (err)
        goto fail;
    if (trap) {
        err = register_die_notifier(&die_notifier);
        if (err)
            goto fail;
        die_registered = true;
    }
    err = register_pm_notifier(&pm_notifier);
    if (err)
        goto fail;
    for (i = 0; i < nworkers; ++i) {
        struct task_struct *t = kthread_create(probe_worker, &workers[i], "bitoxin/%u", i);
        if (IS_ERR(t)) {
            err = PTR_ERR(t);
            goto fail_notifier;
        }
        get_task_struct(t);
        workers[i].task = t;
        if (per_cpu)
            set_cpus_allowed_ptr(t, cpumask_of(workers[i].home_cpu));
    }
    debug_root = debugfs_create_dir("bitoxin", NULL);
    if (IS_ERR_OR_NULL(debug_root)) {
        err = debug_root ? PTR_ERR(debug_root) : -ENOMEM;
        debug_root = NULL;
        goto fail_notifier;
    }
    status = debugfs_create_file("status", 0400, debug_root, NULL, &status_fops);
    if (IS_ERR_OR_NULL(status)) {
        err = status ? PTR_ERR(status) : -ENOMEM;
        debugfs_remove_recursive(debug_root);
        debug_root = NULL;
        goto fail_notifier;
    }
    for (i = 0; i < nworkers; ++i)
        wake_up_process(workers[i].task);
    pr_info("bitoxin: started backend=%s workers=%u mem_kib=%u passes=%llu freezable=%u trap=%u lane_rounds=%u churn=%u per_cpu=%u panic_on_error=%u\n",
            bx_backend_name(), nworkers, effective_kib, passes, freezable, trap,
            lane_rounds, churn, per_cpu, panic_on_error);
    return 0;
fail_notifier:
    unregister_pm_notifier(&pm_notifier);
fail:
    release_hook();
    release_workers();
    release_die();
    return err;
}

static void __exit bitoxin_exit(void)
{
    debugfs_remove_recursive(debug_root);
    release_hook();
    unregister_pm_notifier(&pm_notifier);
    release_workers();
    release_die();
    pr_info("bitoxin: unloaded pm_prepare=%lld pm_post=%lld failed=%d\n",
            atomic64_read(&pm_prepare), atomic64_read(&pm_post), atomic_read(&abort_run));
}
module_init(bitoxin_init);
module_exit(bitoxin_exit);
MODULE_AUTHOR("zotanika@gmail.com");
MODULE_DESCRIPTION("Preemptible state-integrity probe for concurrent QA scenarios");
MODULE_LICENSE("GPL");
MODULE_VERSION("2.1.0");
