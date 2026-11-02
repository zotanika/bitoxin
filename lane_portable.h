/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Semantic reference: the AArch64 stage table in C. It does not emulate register
 * allocation or exception behaviour, and has no register numbers to decode. */
#ifdef __KERNEL__
#include <linux/bug.h>
#endif
#define BX_LANE_REGS 24
#define BX_BACKEND_NAME "portable-c"
#define BX_LANE_NAMES { "c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8", \
    "c9", "c10", "c11", "c12", "c13", "c14", "c15", "c16", "c17", "c18", "c19", \
    "c20", "c21", "c22", "c23" }
#define BX_LANE_REGNOS { -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, \
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 }
#define BX_TRAP_REGNOS { -1, -1, -1, -1 }

static inline bx_u64 bx_lane_ref_step(unsigned k, bx_u64 v)
{
    return bx_a64_step(k, v);
}

static inline void bx_trap_now(bx_u64 kind, bx_u64 a, bx_u64 b, bx_u64 c)
{
    (void)kind; (void)a; (void)b; (void)c;
#ifdef __KERNEL__
    BUG();
#else
    __builtin_trap();
#endif
}

static inline bx_u64 bx_lane(bx_u64 token, bx_u64 check, bx_u32 rounds,
                             bx_u64 *snapshot, bx_u32 *status)
{
    volatile bx_u64 regs[BX_LANE_REGS];
    bx_u64 v = token;
    unsigned k;
    if ((((token >> (check & 7U)) ^ (check >> 8)) & 1U) != 0) {
        *status = BX_LANE_MEMORY;
        if (!snapshot)
            bx_trap_now(BX_LANE_MEMORY, token, 0, check);
        return token;
    }
    while (rounds--) {
        for (k = 0; k < BX_LANE_REGS; ++k) {
            v = bx_lane_ref_step(k, v);
            if ((int)k == BX_LANE_FAULT)
                v ^= 1U;
            regs[k] = v;
        }
        if (v != token) {
            *status = BX_LANE_REGISTER;
            if (!snapshot)
                bx_trap_now(BX_LANE_REGISTER, token, 0, check);
            for (k = 0; k < BX_LANE_REGS; ++k)
                snapshot[k] = regs[k];
            return v;
        }
    }
    *status = BX_LANE_OK;
    return v;
}
