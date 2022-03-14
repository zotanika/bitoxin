/*
 * bitoxin.c
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/random.h>
#include <linux/string.h>
#include <linux/module.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/kthread.h>
#include <linux/delay.h>
#include <linux/lfsrtabs.h>

MODULE_AUTHOR("zotanika@gmail.com");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("bitoxin: probabilistic experimental algorithm accelerating unknown system vulnerabilities to be exposed");

#define NR_INFINITE	0x7FFFFFFF
#define MAX_THREAD	8
#define MAX_SPACE	(0x8000 * PAGE_SIZE)

#define HOOK_SIZE	(0x200)
#define HOOK_DEGREE	12

#define BURST_TEST	NR_INFINITE
#define	BURST_SIZE	MAX_SPACE
#define BURST_THREAD	4

typedef enum {
	UNINIT	= 0,
	IDLING	= (1UL << 0),
	RUNNING	= (1UL << 1),
	HOOKING	= (1UL << 2),
	MIXING	= (1UL << 1) | (1UL << 2)
} bx_state_t;

/* bitoxin_ctx which must describe a complete single instance.
 */
struct bitoxin_ctx {
	spinlock_t		    lock;
	bx_state_t		    state;
	unsigned int		nr_test;
	unsigned int		sz_test;
	unsigned int		nr_thread;	
	/* thread monitoring each bitoxin sessions
     */
	struct task_struct* self;
	struct completion	done;
};

unsigned int __bx_hook = false;
EXPORT_SYMBOL(__bx_hook);

/* bitoxin_ctx instance */
static struct bitoxin_ctx* bx_inst;
/* bitoxin running thread counter */
static atomic_t bx_running = ATOMIC_INIT(0);

/* core algorithm written in asm
 */
static noinline void
____bitoxin(char *buf, unsigned int *lfsr, unsigned int *ppoly)
{
#ifdef CONFIG_ARM64
	asm volatile(
	"	ldr	w3, [%2]\n"
	"	ldr	w2, [%1]\n"
	"	and	w4, w2, #1\n"
	"	neg	w4, w4\n"
	"	and	w4, w3, w4\n"
	"	eor	w2, w4, w2, lsr #1\n"
	"	str	w2, [%1]\n"
	"	lsr	w4, w2, #3\n"
	"	ldrb	w3, [%0, x4]\n"
	"	and	w4, w2, #7\n"
	"	mov	w5, #1\n"
	"	lsl	w5, w5, w4\n"
	"	and	w5, w3, w5\n"
	"	lsr	w5, w5, w4\n"
	"	mov	x6, x5\n"
	"	mov	x7, x6\n"
	"	mov	x8, x7\n"
	"	mov	x9, x8\n"
	"	mov	x10, x9\n"
	"	mov	x11, x10\n"
	"	mov	x12, x11\n"
	"	mov	x13, x12\n"
	"	mov	x14, x13\n"
	"	mov	x15, x14\n"
	"	mov	x16, x15\n"
	"	mov	x17, x16\n"
	"	mov	x18, x17\n"
	"	udiv	%0, %0, x18\n"
	"	lsl	w5, w5, w4\n"
	"	bic	w3, w3, w5\n"
	"	lsr	w4, w2, #3\n"
	"	strb	w3, [%0, x4]\n"
	:
	: "r" (buf), "r" (lfsr),"r" (ppoly)
	: "cc", "memory");
#else
	asm volatile(
	"	ldr	r3, [%2]\n"
	"	ldr	r2, [%1]\n"
	"	and	r4, r2, #1\n"
	"	neg	r4, r4\n"
	"	and	r4, r3, r4\n"
	"	eor	r2, r4, r2, lsr #1\n"
	"	str	r2, [%1]\n"
	"	lsr	r4, r2, #3\n"
	"	ldrb	r3, [%0, r4]\n"
	"	and	r4, r2, #7\n"
	"	mov	r5, #1\n"
	"	lsl	r5, r5, r4\n"
	"	and	r5, r3, r5\n"
	"	lsr	r5, r5, r4\n"
	"	teq	r5, #1\n"
	"	bne	2f\n"
	"1:	lsl	r5, r5, r4\n"
	"	bic	r3, r3, r5\n"
	"	lsr	r4, r2, #3\n"
	"	strb	r3, [%0, r4]\n"
	"	b	3f\n"
	"2:	mov	%0, #0\n"
	"	b	1b\n"
	"3:	nop\n"
	:
	: "r" (buf), "r" (lfsr), "r" (ppoly)
	: "cc", "memory");
#endif
}

static int bitoxin_thread(void *arg)
{
	int ret = 0;
	unsigned int lfsr, ppoly, period, loop_cnt = 0;
	char *ptr_memtest;

	DECLARE_WAIT_QUEUE_HEAD(twq);

	/* calculating arithmetic properties */
	period = __powerof(ilog2(bx_inst->sz_test) + 3);
	ppoly = __ppoly(ilog2(bx_inst->sz_test) + 3);

	/* working thread should not exit until daemon kicks off.
	 */
	wait_event_interruptible(twq, !completion_done(&bx_inst->done));

	/* preparation of bitoxin core loop;
	 * memory allocation up to 2^DEGREE - 1 bits
	 */
	ptr_memtest = vmalloc(bx_inst->sz_test);
	if (ptr_memtest) {
		memset(ptr_memtest, 0xFF, bx_inst->sz_test);

		/* assign a nonzero seed to LFSR */
		while ((lfsr = (get_random_int() & period)) == 0)
			;

		while (loop_cnt++ < period) {
			if (kthread_should_stop())
				break;
			else
				____bitoxin(ptr_memtest, &lfsr, &ppoly);
		}

		vfree(ptr_memtest);
	} else {
		printk(KERN_ERR "%s: Failed to allocate enough memory\n", __func__);
		ret = -ENOMEM;
	}

	if (atomic_dec_and_test(&bx_running))
		complete(&bx_inst->done);

	/* the duty of this thread is only limited to a single turn test.
	 * wait for being killed by monitor.
	 */
	while (!kthread_should_stop()) {
		msleep_interruptible(10);
	}

	return ret;
}

static int bitoxind(void *arg)
{
	int cnt, ret;
	unsigned int loop_cnt = bx_inst->nr_test;
	struct task_struct *t[MAX_THREAD] = { NULL };
	
	DECLARE_WAIT_QUEUE_HEAD(dwq);

	while (!kthread_should_stop()) {
		/* daemon should sleep unless nr_test is nonzero.
		 */		
		wait_event_interruptible(dwq, bx_inst->nr_test);

		/* State transition to RUNNING */
		spin_lock(&bx_inst->lock);
		bx_inst->state |= RUNNING;
		spin_unlock(&bx_inst->lock);

		/* nr_test can be overrided by an user request.
		 */
		do {
			/* get ready to check if whole test sessions are done.
			 */
			reinit_completion(&bx_inst->done);

			/* multiple threads to run core algorithm.
			 * the number of threads does not need to be specified here,
			 * creating threads matching to NR_CPUS is an alternative choice though.
			 */
			for (cnt = 0, atomic_set(&bx_running, 0); cnt < bx_inst->nr_thread; cnt++) {
				t[cnt] = kthread_create(bitoxin_thread, NULL, "bitoxin/%d", cnt);
				if (IS_ERR(t[cnt])) {
					ret = PTR_ERR(t[cnt]);
					return ret;
				}
				atomic_inc(&bx_running);
				wake_up_process(t[cnt]);
			}

			while (wait_for_completion_interruptible_timeout(&bx_inst->done, 100) <= 0) {
				if (kthread_should_stop()) {
					/* user initiated interrupt */
					printk(KERN_NOTICE "%s: user initiated interrupt..\n", __func__);
					loop_cnt = 0;
					complete(&bx_inst->done);
					break;
				} else
					continue;
			}

			/* kill the work threads.
			 */
			for (cnt = 0; cnt < bx_inst->nr_thread; cnt++) {
				kthread_stop(t[cnt]);
			}
		} while (loop_cnt--);

		/* state transition back to IDLING */
		spin_lock(&bx_inst->lock);
		bx_inst->state = IDLING;
		spin_unlock(&bx_inst->lock);
	}

	return 0;
}

static int run_bitoxin(const char *val, struct kernel_param *kp)
{
	int err = -EBUSY;

	if (!bx_inst)
		return -ENOMEM;

	/**
	 * `val` defines test mode.
	 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	 * **burst mode**
	 *   the entire test consumes a relatively huge space.
	 *   memory size, number of threads, number of tests is configurable.
	 *
	 * **hook mode**
	 *   instant test mode consuming local task stack.
	 *   no configuration can override the preset for this mode.
	 *
	 * **mixed mode**
	 *   both burst mode and hook mode are simultaneously conducted.
	 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	 **/
	if (!strncmp(val, "burst", 5)) {
		printk(KERN_NOTICE "%s: setting burst mode(0x%x)..\n", __func__, bx_inst->state);
		switch (bx_inst->state) {
			case UNINIT:
			case HOOKING:
			case MIXING:
				spin_lock(&bx_inst->lock);
				__bx_hook = false;
				bx_inst->state = IDLING;
				spin_unlock(&bx_inst->lock);
			case IDLING:
				bx_inst->self = kthread_create(bitoxind, NULL, "bitoxind");
				if (IS_ERR(bx_inst->self)) {
					printk(KERN_ERR "%s: failed to create daemon..\n", __func__);
					err = PTR_ERR(bx_inst->self);
					spin_lock(&bx_inst->lock);
					bx_inst->self = NULL;
					bx_inst->state = IDLING;
					spin_unlock(&bx_inst->lock);
				} else {
					wake_up_process(bx_inst->self);
					printk(KERN_NOTICE "%s: setting burst mode is done\n", __func__);
					err = 0;
				}
				break;
			case RUNNING:
				printk(KERN_NOTICE "%s: burst mode is already set\n", __func__);
				err = 0;
				break;
			default:
				err = -EBUSY;
				break;
		}
	} else if (!strncmp(val, "hook", 4)) {
		printk(KERN_NOTICE "%s: setting hook mode(0x%x)..\n", __func__, bx_inst->state);
		switch (bx_inst->state) {
			case RUNNING:
			case MIXING:
				kthread_stop(bx_inst->self);
				bx_inst->self = NULL;
			case UNINIT:
			case IDLING:
			case HOOKING:
				spin_lock(&bx_inst->lock);
				__bx_hook = true;
				bx_inst->state = HOOKING;
				spin_unlock(&bx_inst->lock);
				printk(KERN_NOTICE "%s: setting hook mode is done\n", __func__);
				err = 0;
				break;
			default:
				err = -EBUSY;
				break;
		}
	} else if (!strncmp(val, "mixed", 5)) {
		printk(KERN_NOTICE "%s: setting both burst and hook mode enabled(0x%x)..\n", __func__, bx_inst->state);
		switch (bx_inst->state) {
			case RUNNING:
				spin_lock(&bx_inst->lock);
				__bx_hook = true;
				bx_inst->state = MIXING;
				spin_unlock(&bx_inst->lock);
				printk(KERN_NOTICE "%s: setting mixed mode is done\n", __func__);
				break;
			case UNINIT:
			case IDLING:
				spin_lock(&bx_inst->lock);
				__bx_hook = true;
				bx_inst->state = MIXING;
				spin_unlock(&bx_inst->lock);
			case HOOKING:
				bx_inst->self = kthread_create(bitoxind, NULL, "bitoxind");
				if (IS_ERR(bx_inst->self)) {
					printk(KERN_ERR "%s: failed to create daemon..\n", __func__);
					err = PTR_ERR(bx_inst->self);
					spin_lock(&bx_inst->lock);
					bx_inst->self = NULL;
					bx_inst->state = IDLING;
					spin_unlock(&bx_inst->lock);
				} else {
					wake_up_process(bx_inst->self);
					printk(KERN_NOTICE "%s: setting burst mode is done\n", __func__);
					err = 0;
				}
				break;
			case MIXING:
				printk(KERN_NOTICE "%s: mixed mode is already set\n", __func__);
				err = 0;
				break;
			default:
				err = -EBUSY;
				break;
		}
	} else if (!strncmp(val, "stop", 4)) {
		printk(KERN_NOTICE "%s: bitoxin stopping..\n", __func__);
		switch (bx_inst->state) {
			case RUNNING:
			case HOOKING:
			case MIXING:
			case IDLING:
				if (bx_inst->self) {
					kthread_stop(bx_inst->self);
					bx_inst->self = NULL;
				}
				spin_lock(&bx_inst->lock);
				__bx_hook = false;
				bx_inst->state = IDLING;
				spin_unlock(&bx_inst->lock);
				err = 0;
				break;
			case UNINIT:
			default:
				err = -EBUSY;
				break;
		}
	} else {
		printk(KERN_ERR "%s: invalid mode - %s\n", __func__, val);
		err = -EINVAL;
	}

	return err;
}
module_param_call(mode, run_bitoxin, NULL, NULL, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(mode, "configuring what mode bitoxin runs; 'burst','hook','mixed','stop'");

static int bitoxin_nrtest(const char *val, struct kernel_param *kp)
{
	int num = (int)simple_strtoul((const char *)val, NULL, 10);

	if (!bx_inst)
		return -ENOMEM;

	/* nr_test allows being overrided. */
	spin_lock(&bx_inst->lock);
	bx_inst->nr_test = (num <= 0) ? NR_INFINITE : (unsigned int)num;
	spin_unlock(&bx_inst->lock);
	return 0;
}
module_param_call(num, bitoxin_nrtest, NULL, NULL, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(num, "configuring how many times bitoxin runs");

static int bitoxin_memsz(const char *val, struct kernel_param *kp)
{
	int size = (int)simple_strtoul((const char *)val, NULL, 10);

	if (!bx_inst)
		return -ENOMEM;

	if (bx_inst->state == IDLING) {
		int tnr = bx_inst->nr_thread;
		/* space where each thead should manage */
		size = (int)((size << 10) / tnr);
		spin_lock(&bx_inst->lock);
		bx_inst->sz_test = (size <= 0) ? MAX_SPACE : min_t(unsigned int, size, MAX_SPACE);
		spin_unlock(&bx_inst->lock);
		return 0;
	} else 
		return -EBUSY;
}
module_param_call(size, bitoxin_memsz, NULL, NULL, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(size, "configuring how large space bitoxin runs(in Kbyte unit)");

static int bitoxin_nrthread(const char *val, struct kernel_param *kp)
{
	int num = (int)simple_strtoul((const char *)val, NULL, 10);

	if (!bx_inst)
		return -ENOMEM;

	if (bx_inst->state == IDLING) {
		unsigned int oldnr = bx_inst->nr_thread;
		unsigned int oldsz = bx_inst->sz_test;
		unsigned int newnr = (num <= 0) ? MAX_THREAD : min_t(unsigned int, num, MAX_THREAD);
		/* space previous set in byte unit */
		oldsz *= oldnr;
		spin_lock(&bx_inst->lock);
		bx_inst->nr_thread = newnr;
		bx_inst->sz_test = oldsz / newnr;
		spin_unlock(&bx_inst->lock);
		return 0;
	} else
		return -EBUSY;
}
module_param_call(thread, bitoxin_nrthread, NULL, NULL, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(thread, "configuring how many threads split bitoxin job");

/**
 * function called back by hooker set in several linux kernel pinpoints
  */
asmlinkage __visible void __bitoxin(void)
{
	unsigned int lfsr, loop_cnt = 0;
	unsigned int period = __POWEROF(HOOK_DEGREE);
	unsigned int ppoly = __PPOLY(HOOK_DEGREE);
	/* consuming task stack */
	char ptr_memtest[HOOK_SIZE];

	if (!bx_inst)
		return;

	memset(ptr_memtest, 0xFF, HOOK_SIZE);

	/* assign a nonzero seed to LFSR */
	while ((lfsr = (get_random_int() & period)) == 0)
		;

	while (loop_cnt++ <= period)
		____bitoxin(ptr_memtest, &lfsr, &ppoly);
}
EXPORT_SYMBOL(__bitoxin);

static int __init init_bitoxin(void)
{
	/* instance setup */
	bx_inst = kzalloc(sizeof(struct bitoxin_ctx), GFP_ATOMIC);
	if (bx_inst == NULL)
		return -ENOMEM;

	/* initialization */
	*bx_inst = (struct bitoxin_ctx) {
		.lock		= __SPIN_LOCK_UNLOCKED(bx_inst->lock), 
		.state		= UNINIT,
		.nr_test	= BURST_TEST,
		.sz_test	= BURST_SIZE,
		.nr_thread	= BURST_THREAD,
		.self		= NULL,
		.done		= COMPLETION_INITIALIZER(bx_inst->done),
	};
	return 0;
}

static void __exit exit_bitoxin(void)
{
	if (bx_inst != NULL) {
		if (bx_inst->self) {
			kthread_stop(bx_inst->self);
			bx_inst->self = NULL;
		}
		kfree(bx_inst);
	}
}
module_init(init_bitoxin);
module_exit(exit_bitoxin);
