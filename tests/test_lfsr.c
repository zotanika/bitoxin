/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include "bitoxin_lane.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/* Independent linear-map exponentiation verifies full order without walking
 * 2^30 states. A wrong tap or shift direction fails the period factor tests. */
static bx_u32 apply(const bx_u32 map[32], bx_u32 x)
{
    bx_u32 out = 0;
    unsigned bit = 0;
    while (x) { if (x & 1U) out ^= map[bit]; ++bit; x >>= 1; }
    return out;
}
static bx_u32 advance(unsigned degree, bx_u32 tap, bx_u32 steps)
{
    bx_u32 map[32], squared[32], value = 1;
    for (unsigned j = 0; j < degree; ++j)
        map[j] = j == 0 ? tap : 1U << (j - 1);
    while (steps) {
        if (steps & 1U) value = apply(map, value);
        for (unsigned j = 0; j < degree; ++j) squared[j] = apply(map, map[j]);
        for (unsigned j = 0; j < degree; ++j) map[j] = squared[j];
        steps >>= 1;
    }
    return value;
}
int main(void)
{
    for (unsigned degree = 9; degree <= 30; ++degree) {
        bx_u32 bytes = 1U << (degree - 3), period = (1U << degree) - 1;
        unsigned char *buffer = malloc(bytes);
        struct bx_probe p;
        assert(buffer && bx_init(&p, buffer, bytes, 1) == BX_OK);
        if (advance(degree, p.taps, period) != 1) {
            fprintf(stderr, "Non-closing LFSR: degree=%u taps=%x\n", degree, p.taps);
            abort();
        }
        bx_u32 n = period;
        for (bx_u32 factor = 2; factor <= n / factor; ++factor) {
            if (n % factor) continue;
            assert(advance(degree, p.taps, period / factor) != 1);
            do { n /= factor; } while (n % factor == 0);
        }
        if (n > 1) assert(advance(degree, p.taps, period / n) != 1);
        free(buffer);
    }
    for (unsigned i = 0; i < 64; ++i) {
        bx_u64 v = 1ULL << i;
        assert(bx_register_lane(v) == v);
        assert(bx_register_lane(~v) == ~v);
    }
    for (bx_u64 i = 0; i < 10000; ++i) {
        bx_u64 v = i * 0x9e3779b97f4a7c15ULL;
        assert(bx_register_lane(v) == v);
    }
    puts("PASS all 22 LFSR orders and 10128 register-lane inputs");
    return 0;
}
