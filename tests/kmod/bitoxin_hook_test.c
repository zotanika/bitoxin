// SPDX-License-Identifier: GPL-2.0-or-later
/* Test-only caller of BITOXIN_PROBE() from timer (softirq) and process context.
 * Never shipped: the guest checks load it next to bitoxin_qa (threads=0). */
#define BITOXIN_PROBES
#include <linux/module.h>
#include <linux/timer.h>
#include <linux/kthread.h>
#include <linux/delay.h>
#include <linux/version.h>
#include "bitoxin_hook.h"

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 2, 0)
#define bx_timer_stop timer_delete_sync
#else
#define bx_timer_stop del_timer_sync
#endif

static bool timer_only;
module_param(timer_only, bool, 0444);
MODULE_PARM_DESC(timer_only, "Call the probe only from the timer (softirq) context");

static struct timer_list timer;
static struct task_struct *caller;
static bool stopping;

static void bx_test_timer(struct timer_list *t)
{
    (void)t;
    BITOXIN_PROBE();
    if (!READ_ONCE(stopping))
        mod_timer(&timer, jiffies + msecs_to_jiffies(10));
}

static int bx_test_thread(void *unused)
{
    (void)unused;
    while (!kthread_should_stop()) {
        BITOXIN_PROBE();
        msleep(5);
    }
    return 0;
}

static int __init bx_test_init(void)
{
    timer_setup(&timer, bx_test_timer, 0);
    mod_timer(&timer, jiffies + msecs_to_jiffies(10));
    if (timer_only)
        return 0;
    caller = kthread_run(bx_test_thread, NULL, "bitoxin-hook-test");
    if (IS_ERR(caller)) {
        WRITE_ONCE(stopping, true);
        bx_timer_stop(&timer);
        return PTR_ERR(caller);
    }
    return 0;
}

static void __exit bx_test_exit(void)
{
    if (!IS_ERR_OR_NULL(caller))
        kthread_stop(caller);
    WRITE_ONCE(stopping, true);
    bx_timer_stop(&timer);   /* waits for a running callback; it re-arms no more */
}
module_init(bx_test_init);
module_exit(bx_test_exit);
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("BITOXIN hook test caller");
