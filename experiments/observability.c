/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Enumerated fault experiment; no fault injection is exposed in production. */
#include "bitoxin_core.h"
#include <stdio.h>
#include <stdlib.h>

#define BYTES 64U
#define BITS (8U * BYTES)

static void require(int ok, const char *why)
{
    if (!ok) { fprintf(stderr, "experiment failure: %s\n", why); exit(1); }
}
static void clean_step(struct bx_probe *p)
{
    require(bx_run(p, 1) == BX_OK, "fault-free preparation/control");
}
static void prepare(struct bx_probe *p, unsigned char *b,
                    unsigned seed, unsigned direction, unsigned visits,
                    unsigned verified)
{
    require(bx_init(p, b, BYTES, seed) == BX_OK, "initialization");
    if (direction) for (unsigned i = 0; i < BITS + BYTES; ++i) clean_step(p);
    require(p->passes == direction, "direction");
    for (unsigned i = 0; i < visits + verified; ++i) clean_step(p);
    require(p->walked == visits && p->verified == verified, "boundary");
}
static int observe(struct bx_probe *p, unsigned target_pass,
                   int walk_only, unsigned *attempts)
{
    while (p->passes < target_pass && !(walk_only && p->phase == BX_VERIFY)) {
        require(*attempts < 2U * (BITS + BYTES), "finite observation horizon");
        ++*attempts;
        int result = bx_run(p, 1);
        require(result == BX_OK || result == BX_DATA_ERROR, "unexpected failure type");
        if (result == BX_DATA_ERROR) return 1;
    }
    return 0;
}
static void emit(const char *experiment, const char *policy, unsigned seed,
                 unsigned direction, unsigned boundary, int bit, int current,
                 int following, unsigned attempts, const struct bx_probe *p)
{
    printf("%s,%s,%u,%u,%u,%d,%d,%d,%u,%s,%u\n", experiment, policy,
           seed, direction, boundary, bit, current, following, attempts,
           p->error.code == BX_OK ? "none" : p->error.phase == BX_WALK ? "walk" : "verify",
           p->error.code == BX_OK ? 0U : p->error.bit);
}
int main(void)
{
    const unsigned seeds[] = {1, 17, 255};
    const unsigned visits[] = {0, 128, 256, 384, 512};
    const unsigned scans[] = {0, 16, 32, 48, 63};
    const char *policies[] = {"retain_scan", "walk_only", "reset_replay"};
    puts("experiment,policy,seed,direction,boundary,bit,current_detected,following_detected,attempts,phase,reported_bit");
    for (unsigned d = 0; d < 2; ++d) for (unsigned s = 0; s < 3; ++s) {
        for (unsigned k = 0; k < 5; ++k) for (unsigned mode = 0; mode < 3; ++mode) {
            for (int bit = -1; bit < (int)BITS; ++bit) {
                unsigned char buffer[BYTES];
                struct bx_probe p;
                unsigned attempts = 0;
                prepare(&p, buffer, seeds[s], d, visits[k], 0);
                if (bit >= 0) buffer[(unsigned)bit / 8] ^= 1U << ((unsigned)bit % 8);
                if (mode == 2) prepare(&p, buffer, seeds[s], d, visits[k], 0);
                int detected = observe(&p, d + 1, mode == 1, &attempts);
                emit("walk_boundary", policies[mode], seeds[s], d, visits[k], bit,
                     detected, detected, attempts, &p);
            }
        }
        for (unsigned q = 0; q < 5; ++q) for (int bit = -1; bit < (int)BITS; ++bit) {
            unsigned char buffer[BYTES];
            struct bx_probe p;
            unsigned attempts = 0;
            prepare(&p, buffer, seeds[s], d, BITS, scans[q]);
            if (bit >= 0) buffer[(unsigned)bit / 8] ^= 1U << ((unsigned)bit % 8);
            int current = observe(&p, d + 1, 0, &attempts);
            int following = current;
            if (!current) following = observe(&p, d + 2, 0, &attempts);
            emit("scan_boundary", "retain_scan", seeds[s], d, scans[q], bit,
                 current, following, attempts, &p);
        }
    }
    return 0;
}
