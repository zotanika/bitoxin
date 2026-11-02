/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "../tools/bx_suspend.h"
#include <assert.h>
#include <stdio.h>

int main(void)
{
    struct bx_sleep_sample a = { 5000000000ULL, 7 }, b = a;
    uint64_t slept = 99;
    assert(!bx_suspended(&a, &b, &slept) && slept == 0);
    b.sleep_ns = a.sleep_ns + 500000U;           /* clock-read jitter */
    assert(!bx_suspended(&a, &b, &slept));
    b.sleep_ns = a.sleep_ns - 300U;              /* reads in the other order */
    assert(!bx_suspended(&a, &b, &slept) && slept == 0);
    b.sleep_ns = a.sleep_ns + 2000000000ULL;     /* 2 s suspended */
    assert(bx_suspended(&a, &b, &slept) && slept == 2000000000ULL);
    b = a;
    b.attempts = 8;                              /* freezer-only test or failed attempt */
    assert(bx_suspended(&a, &b, &slept) && slept == 0);
    puts("PASS suspend detection");
    return 0;
}
