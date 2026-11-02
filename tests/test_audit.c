/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include <assert.h>
#include <stdio.h>

static void advance(struct bx_probe *p, bx_u32 ops)
{
    assert(bx_run(p, ops) == BX_OK);
}

int main(void)
{
    unsigned char a[512], b[512];
    struct bx_probe p, q;
    const bx_u32 stops[] = { 0, 1, 777, 4094, 4095, 4096, 4096 + 200 };
    unsigned i, polarity;

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
    p.lfsr ^= 0x10U;
    assert(bx_audit(&p) == BX_STATE_ERROR);
    puts("PASS audit detects a moved traversal state");
    return 0;
}
