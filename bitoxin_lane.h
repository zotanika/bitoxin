/* SPDX-License-Identifier: GPL-2.0-or-later */
#ifndef BITOXIN_LANE_H
#define BITOXIN_LANE_H
#include "bitoxin_core.h"

/* Test builds define BX_LANE_FAULT=k (BX_SIMD_FAULT=k) to flip chain register k
 * right after it is produced. The default -1 emits nothing. */
#ifndef BX_LANE_FAULT
#define BX_LANE_FAULT -1
#endif
#ifndef BX_SIMD_FAULT
#define BX_SIMD_FAULT -1
#endif
#define BX_STR_(x) #x
#define BX_STR(x) BX_STR_(x)

static inline bx_u64 bx_ror64(bx_u64 v, unsigned r)
{
    return (v >> r) | (v << (64U - r));
}

static inline bx_u64 bx_rev64(bx_u64 v)
{
    bx_u64 r = 0;
    unsigned i;
    for (i = 0; i < 8; ++i) { r = (r << 8) | (v & 0xffU); v >>= 8; }
    return r;
}

static inline bx_u64 bx_rbit64(bx_u64 v)
{
    bx_u64 r = 0;
    unsigned i;
    for (i = 0; i < 64; ++i) { r = (r << 1) | (v & 1U); v >>= 1; }
    return r;
}

/* Stage k of the AArch64 chain (also the portable reference). Stages 12..23
 * invert stages 11..0, so stage 23 returns the token. */
static inline bx_u64 bx_a64_step(unsigned k, bx_u64 v)
{
    switch (k) {
    case 0: case 23: return v ^ 0x5555555555555555ULL;
    case 1: return bx_ror64(v, 17);
    case 2: return v + 0x7b1U;
    case 3: case 20: return ~v;
    case 4: case 19: return v ^ (v >> 32);
    case 5: case 18: return bx_rbit64(v);
    case 6: case 17: return v ^ 0x0f0f0f0f0f0f0f0fULL;
    case 7: return bx_ror64(v, 41);
    case 8: return v - 0x3c5U;
    case 9: case 14: return bx_rev64(v);
    case 10: case 13: return v ^ (v << 32);
    case 11: case 12: return v ^ 0x00ff00ff00ff00ffULL;
    case 15: return v + 0x3c5U;
    case 16: return bx_ror64(v, 23);
    case 21: return v - 0x7b1U;
    default: return bx_ror64(v, 47);
    }
}

/* Tasks 3 and 4 add the AArch64 and RISC-V branches here. */
#include "lane_portable.h"
#endif
