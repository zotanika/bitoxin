/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static void until_pass(struct bx_probe *p, bx_u64 pass, unsigned budget)
{
    unsigned calls = 0;
    while (p->passes < pass) {
        assert(bx_run(p, budget) == BX_OK);
        assert(++calls < 100000);
    }
}

int main(void)
{
    struct bx_probe p, q;
    unsigned char a[512], b[512], saved[512];
    unsigned i;

    /* A boundary error or omitted zero bit must fail exact end-state checks. */
    assert(bx_init(&p, a, 512, 1) == BX_OK);
    assert(bx_run(&p, 4095) == BX_OK);
    assert(p.phase == BX_WALK && p.walked == 4095);
    assert(a[0] == 1);
    for (i = 1; i < sizeof(a); ++i) assert(a[i] == 0);
    assert(bx_run(&p, 1) == BX_OK);
    assert(p.phase == BX_VERIFY && a[0] == 0 && p.lfsr == 1);
    until_pass(&p, 1, 17);
    assert(p.operations == 4096 + 512);
    until_pass(&p, 2, 37);
    for (i = 0; i < sizeof(a); ++i) assert(a[i] == 255);
    puts("PASS full cycle, zero bit, reverse direction and closure");

    /* Chunk/scheduling boundaries must not restart or reinitialize a walk. */
    assert(bx_init(&p, a, 512, 123) == BX_OK);
    assert(bx_init(&q, b, 512, 123) == BX_OK);
    until_pass(&p, 3, 1);
    until_pass(&q, 3, 65536);
    assert(memcmp(a, b, sizeof(a)) == 0 && p.operations == q.operations);
    assert(p.lfsr == 123 && q.lfsr == 123);
    puts("PASS chunked continuation equals uninterrupted execution");

    /* A wrong bit on the next visit is detected before it can be overwritten. */
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    a[34] &= (unsigned char)~1U; /* degree-9 first state: 0x110 = bit 272 */
    assert(bx_run(&p, 1) == BX_DATA_ERROR);
    assert(p.error.bit == 272 && p.error.expected == 1 && p.error.observed == 0);
    memcpy(saved, a, sizeof(a));
    assert(bx_run(&p, 999) == BX_DATA_ERROR);
    assert(memcmp(saved, a, sizeof(a)) == 0);
    puts("PASS early corruption and latched failure");

    /* Corruption after a visit must survive until verification and be found. */
    assert(bx_init(&p, a, 512, 1) == BX_OK);
    assert(bx_run(&p, 4096) == BX_OK);
    a[200] ^= 0x80;
    assert(bx_run(&p, 512) == BX_DATA_ERROR);
    assert(p.error.phase == BX_VERIFY && p.error.bit == 1600);
    assert(p.error.expected == 0 && p.error.observed == 128);
    puts("PASS late corruption in verification");

    /* The inverse direction must detect 0 -> 1 before touching that location. */
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    until_pass(&p, 1, 4096);
    a[34] |= 1;
    assert(bx_run(&p, 1) == BX_DATA_ERROR);
    assert(p.error.expected == 0 && p.error.observed == 1);
    puts("PASS opposite-polarity corruption");

    assert(bx_init(&p, a, 64, 1) == BX_OK);
    p.lfsr = 0;
    assert(bx_run(&p, 1) == BX_STATE_ERROR);
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    assert(bx_run(&p, 511) == BX_OK);
    p.lfsr = 2;
    assert(bx_run(&p, 1) == BX_STATE_ERROR);
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    p.walked = 999;
    assert(bx_run(&p, 1) == BX_STATE_ERROR);
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    p.verified = 1; /* Would otherwise silently skip verification of byte zero. */
    assert(bx_run(&p, 1) == BX_STATE_ERROR);
    puts("PASS corrupted cursor and non-closing LFSR");

    assert(bx_init(&p, a, 0, 1) == BX_BAD_CONFIG);
    assert(bx_init(&p, a, 63, 1) == BX_BAD_CONFIG);
    assert(bx_init(&p, a, 65, 1) == BX_BAD_CONFIG);
    assert(bx_init(&p, a, BX_MAX_BYTES + 1, 1) == BX_BAD_CONFIG);
    assert(bx_init(&p, a, 64, 0) == BX_BAD_CONFIG);
    assert(bx_init(&p, a, 64, 512) == BX_BAD_CONFIG);
    assert(bx_init(&p, NULL, 64, 1) == BX_BAD_CONFIG);
    assert(bx_init(NULL, a, 64, 1) == BX_BAD_CONFIG);
    puts("PASS invalid sizes, seeds and pointers rejected");

    /* A corrupted tap mask is rejected. */
    assert(bx_init(&p, a, 512, 1) == BX_OK);
    assert(bx_run(&p, 100) == BX_OK);
    p.taps ^= 0x40U;
    assert(bx_run(&p, 1) == BX_STATE_ERROR);
    assert(bx_init(&p, a, 512, 1) == BX_OK);
    assert(bx_set_lane(&p, 0, 0) == BX_BAD_CONFIG);
    assert(bx_set_lane(&p, BX_MAX_ROUNDS + 1, 0) == BX_BAD_CONFIG);
    assert(bx_set_lane(&p, 7, 0) == BX_OK && p.rounds == 7);
    until_pass(&p, 2, 333);
    assert(p.error.lane_index == -1);
    puts("PASS memory-resident taps and lane rounds");

    /* Rebinding is a pass-boundary operation that keeps counters and polarity. */
    assert(bx_init(&p, a, 512, 9) == BX_OK);
    until_pass(&p, 1, 4096);
    memset(b, 0x5a, sizeof(b));
    assert(bx_rebind(&p, b) == BX_OK);
    for (i = 0; i < sizeof(b); ++i) assert(b[i] == 0);
    until_pass(&p, 2, 999);
    memset(a, 0x5a, sizeof(a));
    assert(bx_rebind(&p, a) == BX_OK); /* even pass: the 0xff polarity */
    for (i = 0; i < sizeof(a); ++i) assert(a[i] == 0xff);
    until_pass(&p, 4, 999);
    assert(p.passes == 4 && p.operations == 4U * 4608U && p.buffer == a);
    assert(bx_run(&p, 10) == BX_OK);
    assert(bx_rebind(&p, b) == BX_BAD_CONFIG);
    assert(bx_rebind(&p, NULL) == BX_BAD_CONFIG);
    assert(p.error.code == BX_OK && p.buffer == a);
    puts("PASS rebind at pass boundaries only, both polarities");

    /* A latched error is returned unchanged; the new buffer is not touched. */
    assert(bx_init(&p, a, 512, 9) == BX_OK);
    until_pass(&p, 1, 4096);
    a[7] ^= 0x10;
    assert(bx_audit(&p) == BX_DATA_ERROR);
    assert(p.error.bit == BX_AUDIT_UNLOCATED);
    assert(p.error.expected == 0 && p.error.observed == 1);
    memset(b, 0x5a, sizeof(b));
    assert(bx_rebind(&p, b) == BX_DATA_ERROR);
    assert(bx_rebind(&p, NULL) == BX_DATA_ERROR);
    assert(p.error.code == BX_DATA_ERROR && p.error.bit == BX_AUDIT_UNLOCATED);
    assert(p.error.expected == 0 && p.error.observed == 1 && p.buffer == a);
    for (i = 0; i < sizeof(b); ++i) assert(b[i] == 0x5a);
    puts("PASS rebind returns a latched error unchanged");

    /* The released buffer is checked: a change since the verify is not lost. */
    assert(bx_init(&p, a, 512, 9) == BX_OK);
    until_pass(&p, 1, 4096);   /* boundary value 0x00 */
    memset(b, 0x5a, sizeof(b));
    a[300] ^= 0x04;
    assert(bx_rebind(&p, b) == BX_DATA_ERROR);
    assert(p.error.code == BX_DATA_ERROR && p.error.bit == 300U * 8U);
    assert(p.error.expected == 0 && p.error.observed == 4 && p.buffer == a);
    assert(bx_run(&p, 1) == BX_DATA_ERROR && p.error.bit == 300U * 8U);
    assert(bx_init(&q, b, 512, 9) == BX_OK);
    until_pass(&q, 2, 4096);   /* boundary value 0xff */
    b[511] &= 0x7f;
    assert(bx_rebind(&q, a) == BX_DATA_ERROR);
    assert(q.error.bit == 511U * 8U && q.error.expected == 0xff);
    assert(q.error.observed == 0x7f && q.buffer == b);
    puts("PASS rebind checks the released buffer");

    /* Every pass ends with lfsr == seed: a moved cursor there is corruption. */
    assert(bx_init(&p, a, 512, 9) == BX_OK);
    until_pass(&p, 1, 4096);
    memset(b, 0x5a, sizeof(b));
    p.lfsr = 10;
    assert(bx_rebind(&p, b) == BX_STATE_ERROR);
    assert(p.error.code == BX_STATE_ERROR && p.error.expected == 9);
    assert(p.error.observed == 10 && p.buffer == a);
    for (i = 0; i < sizeof(b); ++i) assert(b[i] == 0x5a);
    assert(bx_run(&p, 1) == BX_STATE_ERROR && p.error.observed == 10);
    puts("PASS rebind latches a moved boundary cursor");

    /* A corrupted size is a state error, not an overrun of the new buffer. */
    assert(bx_init(&p, a, 512, 9) == BX_OK);
    until_pass(&p, 1, 4096);
    memset(b, 0x5a, sizeof(b));
    p.bytes *= 2U;
    assert(bx_rebind(&p, b) == BX_STATE_ERROR);
    assert(p.error.code == BX_STATE_ERROR && p.buffer == a);
    for (i = 0; i < sizeof(b); ++i) assert(b[i] == 0x5a);
    puts("PASS rebind validates the probe before writing");

    /* The closing walk step leaves lfsr == seed for the whole verify phase. */
    assert(bx_init(&p, a, 64, 1) == BX_OK);
    assert(bx_run(&p, 512 + 3) == BX_OK);
    assert(p.phase == BX_VERIFY && p.verified == 3);
    p.lfsr = 2;
    assert(bx_run(&p, 1) == BX_STATE_ERROR && p.verified == 3);
    assert(p.error.phase == BX_VERIFY && p.error.expected == 1 && p.error.observed == 2);
    puts("PASS verify rejects a moved traversal state");
    puts("ALL CORE TESTS PASSED");
    return 0;
}
