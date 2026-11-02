/* SPDX-License-Identifier: GPL-2.0-or-later */
/* BITOXIN_PROBE() runs the register chain and a retained per-CPU state check at
 * a BSP-chosen point (clock gating, power-domain or IOMMU code, ...). It runs on
 * the current CPU with preemption disabled and IRQs untouched, is safe in IRQ
 * context, and is a no-op until bitoxin_qa has initialized.
 *
 * In-tree: enable CONFIG_BITOXIN_QA. Out-of-tree module callers: define
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
