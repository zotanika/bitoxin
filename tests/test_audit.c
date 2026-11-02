/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

#define EX_BYTES 64U
#define EX_BITS (EX_BYTES * 8U)

static unsigned char ex[EX_BYTES];

static void advance(struct bx_probe *p, bx_u32 ops)
{
    assert(bx_run(p, ops) == BX_OK);
}

static void flip(bx_u32 bit)
{
    ex[bit >> 3] ^= (unsigned char)(1U << (bit & 7U));
}

/* A clean audit returns OK and changes nothing but the audit count. */
static void audit_clean(struct bx_probe *p)
{
    struct bx_probe before;
    unsigned char saved[EX_BYTES];
    memcpy(&before, p, sizeof(before));
    memcpy(saved, ex, sizeof(saved));
    assert(bx_audit(p) == BX_OK);
    assert(p->audits == before.audits + 1);
    before.audits = p->audits;
    assert(memcmp(&before, p, sizeof(before)) == 0);
    assert(memcmp(saved, ex, sizeof(saved)) == 0);
}

/* Every single-bit flip is caught: located when the bit was visited or its byte
 * is in the verify phase, counted when it was not visited yet. */
static void audit_flips(const struct bx_probe *p, const unsigned char *visited)
{
    bx_u32 b;
    for (b = 0; b < EX_BITS; ++b) {
        struct bx_probe d = *p;
        flip(b);
        assert(bx_audit(&d) == BX_DATA_ERROR);
        flip(b);
        assert(d.error.phase == p->phase && d.audits == p->audits);
        if (p->phase == BX_VERIFY) {
            bx_u8 want = p->expected ? 0 : 0xff;
            assert(d.error.bit == (b & ~7U) && d.error.expected == want);
            assert(d.error.observed == (bx_u8)(want ^ (1U << (b & 7U))));
        } else if (visited[b]) {
            assert(d.error.bit == b);
            assert(d.error.expected == (p->expected ^ 1U));
            assert(d.error.observed == p->expected);
        } else {
            assert(d.error.bit == BX_AUDIT_UNLOCATED);
            assert(d.error.expected == p->walked);
            assert(d.error.observed == p->walked + 1U);
        }
    }
}

/* Every walked and verified position of a small buffer, both polarities. The
 * visited set comes from bx_run's cursor, independently of the audit's replay. */
static void exhaustive(void)
{
    static const bx_u32 seeds[] = { 1, 0x100, 0x1ff };
    struct bx_probe p, d, before;
    unsigned char visited[EX_BITS];
    unsigned s, polarity;
    bx_u32 w, v;

    for (s = 0; s < sizeof(seeds) / sizeof(seeds[0]); ++s)
        for (polarity = 0; polarity < 2; ++polarity) {
            assert(bx_init(&p, ex, EX_BYTES, seeds[s]) == BX_OK);
            if (polarity) advance(&p, EX_BITS + EX_BYTES);
            assert(p.passes == polarity && p.expected == (polarity ^ 1U));
            memset(visited, 0, sizeof(visited));
            for (w = 0; w < EX_BITS; ++w) {
                assert(p.phase == BX_WALK && p.walked == w);
                audit_clean(&p);
                audit_flips(&p, visited);
                if (w == EX_BITS - 1) {
                    /* Index 0 is outside the LFSR cycle: only the closing
                     * step visits it, so it is the one unvisited bit left. */
                    d = p;
                    flip(0);
                    assert(bx_audit(&d) == BX_DATA_ERROR);
                    flip(0);
                    assert(d.error.bit == BX_AUDIT_UNLOCATED);
                    assert(d.error.expected == EX_BITS - 1);
                    assert(d.error.observed == EX_BITS);
                }
                advance(&p, 1);
                assert(!visited[p.cursor]);
                visited[p.cursor] = 1;
            }
            assert(p.cursor == 0 && p.lfsr == p.seed);
            for (v = 0; v < EX_BYTES; ++v) {
                assert(p.phase == BX_VERIFY && p.verified == v);
                audit_clean(&p);
                audit_flips(&p, visited);
                /* The closing step leaves lfsr == seed for the whole verify. */
                d = p;
                d.lfsr = p.seed == 1 ? 2 : 1;
                assert(bx_audit(&d) == BX_STATE_ERROR);
                assert(d.error.expected == p.seed && d.error.observed == d.lfsr);
                advance(&p, 1);
            }
            assert(p.passes == polarity + 1U && p.phase == BX_WALK);
            assert(p.walked == 0 && p.audits == EX_BITS + EX_BYTES);
        }
    puts("PASS audit exhaustive: clean, every flip, every position");

    /* A latched error is returned unchanged and is not counted as an audit. */
    assert(bx_init(&p, ex, EX_BYTES, 1) == BX_OK);
    ex[34] &= (unsigned char)~1U; /* degree-9 first state: 0x110 = bit 272 */
    assert(bx_run(&p, 1) == BX_DATA_ERROR && p.error.bit == 272);
    memcpy(&before, &p, sizeof(before));
    assert(bx_audit(&p) == BX_DATA_ERROR);
    assert(memcmp(&before, &p, sizeof(before)) == 0);
    assert(bx_audit(NULL) == BX_BAD_CONFIG);
    puts("PASS audit keeps a latched error and rejects a NULL probe");
}

int main(void)
{
    unsigned char a[512], b[512];
    struct bx_probe p, q;
    const bx_u32 stops[] = { 0, 1, 777, 4094, 4095, 4096, 4096 + 200 };
    unsigned i, polarity;
    bx_u32 lfsr;

    for (polarity = 0; polarity < 2; ++polarity)
        for (i = 0; i < sizeof(stops) / sizeof(stops[0]); ++i) {
            assert(bx_init(&p, a, 512, 5) == BX_OK);
            while (p.passes < polarity) advance(&p, 4096);
            if (stops[i]) advance(&p, stops[i]);
            assert(bx_audit(&p) == BX_OK && p.audits == 1);
        }
    puts("PASS audit accepts clean states in both polarities");

    assert(bx_init(&p, a, 512, 5) == BX_OK);
    advance(&p, 100);
    a[p.cursor >> 3] ^= (unsigned char)(1U << (p.cursor & 7U));
    assert(bx_audit(&p) == BX_DATA_ERROR && p.error.bit == p.cursor);
    puts("PASS audit locates a visited-bit error");

    /* The twin's next index is still unvisited in p. */
    assert(bx_init(&p, a, 512, 5) == BX_OK && bx_init(&q, b, 512, 5) == BX_OK);
    advance(&p, 100);
    advance(&q, 101);
    a[q.cursor >> 3] ^= (unsigned char)(1U << (q.cursor & 7U));
    assert(bx_audit(&p) == BX_DATA_ERROR);
    assert(p.error.bit == BX_AUDIT_UNLOCATED);
    assert(p.error.expected == 100 && p.error.observed == 101);
    puts("PASS audit counts an unvisited-bit error");

    assert(bx_init(&p, a, 512, 5) == BX_OK);
    advance(&p, 4096 + 300);
    a[10] ^= 0x04;
    assert(bx_audit(&p) == BX_DATA_ERROR && p.error.bit == 80);
    puts("PASS audit rechecks verified bytes");

    assert(bx_init(&p, a, 512, 5) == BX_OK);
    advance(&p, 50);
    lfsr = p.lfsr;
    p.lfsr ^= 0x10U;
    /* Replay result vs stored state, not the entry check (expected 0). */
    assert(bx_audit(&p) == BX_STATE_ERROR);
    assert(p.error.expected == lfsr && p.error.observed == (lfsr ^ 0x10U));
    puts("PASS audit detects a moved traversal state");

    /* A flipped phase is a state error, reported like bx_run's step checks. */
    assert(bx_init(&p, a, 512, 5) == BX_OK);
    advance(&p, 100);
    p.phase = BX_VERIFY;
    assert(bx_audit(&p) == BX_STATE_ERROR);
    assert(p.error.expected == 512 - 1 && p.error.observed == 0);
    /* verified == 0 here; otherwise the entry check already rejects WALK. */
    assert(bx_init(&p, a, 512, 5) == BX_OK);
    advance(&p, 4096);
    p.phase = BX_WALK;
    assert(bx_audit(&p) == BX_STATE_ERROR);
    assert(p.error.expected == 4096 - 1 && p.error.observed == 4096);
    puts("PASS audit rejects a flipped phase as a state error");

    exhaustive();
    return 0;
}
