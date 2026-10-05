/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Replace only the hardware lane in this test translation unit: a transient
 * high-register-bit error must be caught before changing test memory. */
#include "bitoxin_core.h"
#define BITOXIN_LANE_H
static bx_u64 bx_register_lane(bx_u64 x) { return x ^ (1ULL << 61); }
#include "../bitoxin_core.c"
#include <assert.h>
#include <stdio.h>
int main(void)
{
    unsigned char buffer[64];
    struct bx_probe p;
    assert(bx_init(&p, buffer, 64, 1) == BX_OK);
    assert(bx_run(&p, 1) == BX_REGISTER_ERROR);
    assert(p.error.bit == 272);
    assert((p.error.expected ^ p.error.observed) == (1ULL << 61));
    for (unsigned i = 0; i < sizeof(buffer); ++i) assert(buffer[i] == 255);
    puts("PASS simulated register error is latched before store");
    return 0;
}
