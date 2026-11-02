/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Corrupt the tap mask inside one bx_run call, after the entry check: the
 * per-step reload must catch the derailed LFSR before any out-of-range store. */
#include "bitoxin_core.h"
#include "bitoxin_lane.h"
static struct bx_probe *victim;
static unsigned calls;
static bx_u64 counting_lane(bx_u64 token, bx_u64 check, bx_u32 rounds,
                            bx_u64 *snapshot, bx_u32 *status)
{
    bx_u64 carried = bx_lane(token, check, rounds, snapshot, status);
    if (++calls == 100)
        victim->taps ^= 1U << 20; /* Next state lands far outside a 4096-bit buffer. */
    return carried;
}
#define bx_lane counting_lane
#include "../bitoxin_core.c"
#include <assert.h>
#include <stdio.h>
int main(void)
{
    unsigned char buffer[512];
    struct bx_probe p;
    assert(bx_init(&p, buffer, 512, 1) == BX_OK);
    victim = &p;
    assert(bx_run(&p, 4096) == BX_STATE_ERROR);
    assert(p.walked == 100 && calls == 100);
    assert(p.error.phase == BX_WALK && p.error.observed >= p.bits);
    puts("PASS mid-run tap corruption stops the walk before an out-of-range store");
    return 0;
}
