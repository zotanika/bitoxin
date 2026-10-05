/* SPDX-License-Identifier: GPL-2.0-or-later */
#ifndef BITOXIN_LANE_H
#define BITOXIN_LANE_H
#include "bitoxin_core.h"

/* Identity through a GPR dependency chain, with preemption/IRQs untouched.
 * Declare every scratch register and early-clobber output. Avoid x18 and FP. */
static inline bx_u64 bx_register_lane(bx_u64 input)
{
#if defined(__aarch64__) && !defined(BX_PORTABLE)
    bx_u64 output;
    __asm__ volatile (
        "mvn x9, %[input]\n\t"
        "ror x10, x9, #17\n\t"
        "mov x11, x10\n\t"
        "mvn x12, x11\n\t"
        "ror x13, x12, #47\n\t"
        "mov x14, x13\n\t"
        "mov %[output], x14\n\t"
        : [output] "=&r" (output)
        : [input] "r" (input)
        : "x9", "x10", "x11", "x12", "x13", "x14");
    return output;
#else
    /* Semantic reference, not an emulation of register/exception behavior. */
    volatile bx_u64 value = ~input;
    value = (value >> 17) | (value << 47);
    value = ~value;
    value = (value >> 47) | (value << 17);
    return value;
#endif
}
#endif
