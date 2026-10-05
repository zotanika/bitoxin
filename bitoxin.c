// SPDX-License-Identifier: GPL-2.0-or-later
/* BITOXIN 2: a preemptible state-integrity probe alongside external QA scenarios. */
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
#include "bitoxin_core.h"

static unsigned int threads = 1, mem_kib = 1024, seed = 1, chunk = 4096, pause_ms;
static unsigned long long passes;
static bool freezable = true, panic_on_error;
module_param(threads, uint, 0444);
MODULE_PARM_DESC(threads, "Independent workers (1..32)");
module_param(mem_kib, uint, 0444);
MODULE_PARM_DESC(mem_kib, "Power-of-two KiB per worker; total <=256 MiB");
module_param(seed, uint, 0444);
MODULE_PARM_DESC(seed, "Nonzero first-worker seed, smaller than buffer bit count");
module_param(chunk, uint, 0444);
MODULE_PARM_DESC(chunk, "Operations between stop/freezer/status checks (1..65536)");
module_param(pause_ms, uint, 0444);
MODULE_PARM_DESC(pause_ms, "Optional interruptible pause per chunk (0..1000 ms)");
module_param(passes, ullong, 0444);
MODULE_PARM_DESC(passes, "Verified directional passes per worker; zero runs until unload/error");
module_param(freezable, bool, 0444);
MODULE_PARM_DESC(freezable, "Cooperate with system-suspend freezer (default true)");
module_param(panic_on_error, bool, 0444);
MODULE_PARM_DESC(panic_on_error, "Panic after logging first probe failure (default false)");

struct bx_snapshot {
    u64 passes, operations, boottime_ns;
    u32 seed, walked, verified;
    enum bx_phase phase;
    struct bx_error error;
    const char *state;
};
struct bx_worker {
    struct task_struct *task;
    struct bx_probe probe;
    u8 *buffer;
    unsigned int id;
    struct mutex snapshot_lock;
    struct bx_snapshot snapshot;
};
static struct bx_worker *workers;
static struct dentry *debug_root;
static atomic_t abort_run = ATOMIC_INIT(0);
static atomic64_t pm_prepare = ATOMIC64_INIT(0), pm_post = ATOMIC64_INIT(0);

/* Called outside the probe: readers never race the mutable probe cursor. */
static void publish(struct bx_worker *w, const char *state)
{
    struct bx_probe *p = &w->probe;
    mutex_lock(&w->snapshot_lock);
    w->snapshot = (struct bx_snapshot) {
        .passes = p->passes, .operations = p->operations,
        .boottime_ns = ktime_get_boottime_ns(), .seed = p->seed,
        .walked = p->walked, .verified = p->verified, .phase = p->phase,
        .error = p->error, .state = state,
    };
    mutex_unlock(&w->snapshot_lock);
}

static int probe_worker(void *arg)
{
    struct bx_worker *w = arg;
    const char *state = "stopped";
    if (freezable)
        set_freezable();
    publish(w, "running");
    while (!kthread_should_stop() && !atomic_read(&abort_run)) {
        if (passes && w->probe.passes >= passes) {
            state = "complete";
            break;
        }
        /* kthread_freezable_should_stop also avoids freezer/kthread_stop deadlocks.
         * State is not reinitialized when this call returns after resume. */
        if (freezable && kthread_freezable_should_stop(NULL))
            break;
        if (atomic_read(&abort_run))
            break;
        if (bx_run(&w->probe, chunk) != BX_OK) {
            struct bx_error *e = &w->probe.error;
            state = "failed";
            publish(w, state);
            if (atomic_cmpxchg(&abort_run, 0, 1) == 0) {
                pr_err("bitoxin: failure worker=%u seed=%u pass=%llu phase=%s bit=%u type=%s expected=%016llx observed=%016llx boottime_ns=%llu\n",
                       w->id, w->probe.seed, e->pass,
                       e->phase == BX_WALK ? "walk" : "verify", e->bit,
                       bx_result_name(e->code), e->expected, e->observed,
                       ktime_get_boottime_ns());
                if (panic_on_error)
                    panic("bitoxin: probe failure (see preceding record)");
            }
            break;
        }
        publish(w, "running");
        cond_resched();
        if (pause_ms)
            msleep_interruptible(pause_ms);
    }
    if (atomic_read(&abort_run) && w->probe.error.code == BX_OK)
        state = "aborted";
    publish(w, state);
    pr_info("bitoxin: worker=%u state=%s passes=%llu operations=%llu\n",
            w->id, state, w->probe.passes, w->probe.operations);
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
    if (event == PM_SUSPEND_PREPARE || event == PM_HIBERNATION_PREPARE)
        atomic64_inc(&pm_prepare);
    else if (event == PM_POST_SUSPEND || event == PM_POST_HIBERNATION)
        atomic64_inc(&pm_post);
    return NOTIFY_OK;
}
static struct notifier_block pm_notifier = { .notifier_call = pm_event };

static int status_show(struct seq_file *s, void *unused)
{
    unsigned int i;
    (void)unused;
    seq_printf(s, "{\"schema\":1,\"backend\":\"%s\",\"failed\":%s,\"mem_kib\":%u,\"requested_passes\":%llu,\"chunk\":%u,\"pause_ms\":%u,\"freezable\":%s,\"pm_prepare\":%lld,\"pm_post\":%lld,\"workers\":[",
               bx_backend_name(), atomic_read(&abort_run) ? "true" : "false",
               mem_kib, passes, chunk, pause_ms, freezable ? "true" : "false",
               atomic64_read(&pm_prepare), atomic64_read(&pm_post));
    for (i = 0; i < threads; ++i) {
        struct bx_snapshot snap;
        mutex_lock(&workers[i].snapshot_lock);
        snap = workers[i].snapshot;
        mutex_unlock(&workers[i].snapshot_lock);
        seq_printf(s, "%s{\"id\":%u,\"state\":\"%s\",\"seed\":%u,\"passes\":%llu,\"operations\":%llu,\"phase\":\"%s\",\"walked\":%u,\"verified\":%u,\"boottime_ns\":%llu,\"error\":\"%s\",\"error_bit\":%u,\"expected\":\"%016llx\",\"observed\":\"%016llx\"}",
                   i ? "," : "", i, snap.state, snap.seed, snap.passes,
                   snap.operations, snap.phase == BX_WALK ? "walk" : "verify",
                   snap.walked, snap.verified, snap.boottime_ns,
                   bx_result_name(snap.error.code), snap.error.bit,
                   snap.error.expected, snap.error.observed);
    }
    seq_puts(s, "]}\n");
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

static void release_workers(void)
{
    unsigned int i;
    if (!workers)
        return;
    for (i = 0; i < threads; ++i)
        if (workers[i].task)
            kthread_stop(workers[i].task);
    for (i = 0; i < threads; ++i)
        vfree(workers[i].buffer);
    kfree(workers);
    workers = NULL;
}

static int __init bitoxin_init(void)
{
    unsigned int i;
    int err;
    struct dentry *status;
    if (!threads || threads > 32 || !mem_kib || mem_kib > BX_MAX_BYTES / 1024 ||
        (mem_kib & (mem_kib - 1)) || (u64)mem_kib * threads > 256U * 1024U ||
        !seed || seed >= mem_kib * 8192U || !chunk || chunk > 65536 || pause_ms > 1000)
        return -EINVAL;
    workers = kcalloc(threads, sizeof(*workers), GFP_KERNEL);
    if (!workers)
        return -ENOMEM;
    for (i = 0; i < threads; ++i) {
        struct bx_worker *w = &workers[i];
        u32 worker_seed = 1U + ((seed - 1U + i) % (mem_kib * 8192U - 1U));
        w->id = i;
        mutex_init(&w->snapshot_lock);
        w->buffer = vmalloc((size_t)mem_kib * 1024U);
        if (!w->buffer) { err = -ENOMEM; goto fail; }
        if (bx_init(&w->probe, w->buffer, mem_kib * 1024U, worker_seed) != BX_OK) {
            err = -EINVAL; goto fail;
        }
        publish(w, "ready");
    }
    err = register_pm_notifier(&pm_notifier);
    if (err)
        goto fail;
    for (i = 0; i < threads; ++i) {
        workers[i].task = kthread_create(probe_worker, &workers[i], "bitoxin/%u", i);
        if (IS_ERR(workers[i].task)) {
            err = PTR_ERR(workers[i].task);
            workers[i].task = NULL;
            goto fail_notifier;
        }
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
    for (i = 0; i < threads; ++i)
        wake_up_process(workers[i].task);
    pr_info("bitoxin: started backend=%s threads=%u mem_kib=%u passes=%llu freezable=%u panic_on_error=%u\n",
            bx_backend_name(), threads, mem_kib, passes, freezable, panic_on_error);
    return 0;
fail_notifier:
    unregister_pm_notifier(&pm_notifier);
fail:
    release_workers();
    return err;
}

static void __exit bitoxin_exit(void)
{
    debugfs_remove_recursive(debug_root);
    unregister_pm_notifier(&pm_notifier);
    release_workers();
    pr_info("bitoxin: unloaded pm_prepare=%lld pm_post=%lld failed=%d\n",
            atomic64_read(&pm_prepare), atomic64_read(&pm_post), atomic_read(&abort_run));
}
module_init(bitoxin_init);
module_exit(bitoxin_exit);
MODULE_AUTHOR("zotanika@gmail.com");
MODULE_DESCRIPTION("Preemptible state-integrity probe for concurrent QA scenarios");
MODULE_LICENSE("GPL");
MODULE_VERSION("2.0.0");
