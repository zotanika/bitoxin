/* SPDX-License-Identifier: GPL-2.0-or-later */
/* BITOXIN_PROBE() runs the register chain and a retained per-CPU state check at
 * a BSP-chosen point (clock gating, power-domain or IOMMU code, ...). It runs on
 * the current CPU with preemption disabled and IRQs untouched, may be called in
 * IRQ context, and is a no-op until bitoxin_qa has initialized.
 *
 * Contract for a call site:
 * - RCU must be watching: not in noinstr code, not in the idle path after
 *   ct_cpuidle_enter() (or before ct_cpuidle_exit()), not in early entry code.
 *   Unloading waits for callers with synchronize_rcu().
 * - With trap=1 a failing call traps in place and oopses: in IRQ context, or
 *   with locks held, that ends in a panic or a dead task holding the locks.
 *   Record mode (trap=0) only logs and latches the failure.
 * - The site is __func__: a C identifier, which keeps the status JSON and the
 *   BITOXIN_TRAP record one token (other characters are printed as '?').
 *
 * In-tree: enable CONFIG_BITOXIN_QA. With CONFIG_BITOXIN_QA=m, built-in
 * (vmlinux) callers cannot reach the module and get the no-op (IS_REACHABLE);
 * only module callers get the probe. Out-of-tree module callers: define
 * BITOXIN_PROBES and build with KBUILD_EXTRA_SYMBOLS=<bitoxin>/Module.symvers. */
#ifndef BITOXIN_HOOK_H
#define BITOXIN_HOOK_H
#if IS_REACHABLE(CONFIG_BITOXIN_QA) || defined(BITOXIN_PROBES)
void bitoxin_probe_point(const char *site);
#define BITOXIN_PROBE() bitoxin_probe_point(__func__)
#else
#define BITOXIN_PROBE() do { } while (0)
#endif
#endif
