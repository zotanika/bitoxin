/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Built with -DBX_LANE_FAULT=k: the record snapshot must decode to position k
 * before any test memory changes. Without a fault it prints the chain length. */
#include "bitoxin_core.h"
#include <assert.h>
#include <stdio.h>
#ifndef BX_LANE_FAULT
#define BX_LANE_FAULT -1
#endif

int main(void)
{
    unsigned char buffer[64];
    struct bx_probe p;
    unsigned i;
    bx_u32 rounds;
    if (BX_LANE_FAULT < 0) {
        printf("%d\n", bx_lane_count());
        return 0;
    }
    for (rounds = 1; rounds <= 3; rounds += 2) {
        assert(bx_init(&p, buffer, 64, 1) == BX_OK);
        assert(bx_set_lane(&p, rounds, 0) == BX_OK);
        assert(bx_run(&p, 1) == BX_REGISTER_ERROR);
        assert(p.error.bit == 272);
        assert(p.error.lane_index == BX_LANE_FAULT && !p.error.lane_simd);
        assert((p.error.lane_expected ^ p.error.lane_observed) == 1U);
        for (i = 0; i < sizeof(buffer); ++i) assert(buffer[i] == 255);
        assert(bx_run(&p, 1) == BX_REGISTER_ERROR);
    }
    printf("PASS fault at %s decoded\n", bx_lane_reg_name(BX_LANE_FAULT));
    return 0;
}
