/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Corrupt traversal state inside one bx_run call, after the entry check: the
 * per-step reloads must stop the walk before an out-of-range store (tap mask)
 * or a lane call with zero rounds (which never ends on AArch64). */
#define _POSIX_C_SOURCE 200809L
#include "bitoxin_core.h"
#include "bitoxin_lane.h"
static struct bx_probe *victim;
static unsigned calls;
static int corrupt_rounds;
static bx_u64 counting_lane(bx_u64 token, bx_u64 check, bx_u32 rounds,
                            bx_u64 *snapshot, bx_u32 *status)
{
    bx_u64 carried = bx_lane(token, check, rounds, snapshot, status);
    if (++calls == 100) {
        if (corrupt_rounds)
            victim->rounds = 0;
        else
            victim->taps ^= 1U << 20; /* Next state lands far outside a 4096-bit buffer. */
    }
    return carried;
}
#define bx_lane counting_lane
#include "../bitoxin_core.c"
#include <assert.h>
#include <stdio.h>
#include <unistd.h>
int main(void)
{
    unsigned char buffer[512];
    struct bx_probe p;
    alarm(10); /* A regression must fail, not hang in the lane loop. */
    assert(bx_init(&p, buffer, 512, 1) == BX_OK);
    victim = &p;
    assert(bx_run(&p, 4096) == BX_STATE_ERROR);
    assert(p.walked == 100 && calls == 100);
    assert(p.error.phase == BX_WALK && p.error.observed >= p.bits);
    puts("PASS mid-run tap corruption stops the walk before an out-of-range store");

    assert(bx_init(&p, buffer, 512, 1) == BX_OK);
    calls = 0;
    corrupt_rounds = 1;
    assert(bx_run(&p, 4096) == BX_STATE_ERROR);
    assert(p.walked == 100 && calls == 100);
    assert(p.error.phase == BX_WALK && p.error.expected == BX_MAX_ROUNDS &&
           p.error.observed == 0);
    puts("PASS mid-run zero rounds stops the walk before the lane call");
    return 0;
}
