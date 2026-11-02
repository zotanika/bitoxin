/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Suspend detection for the runner (pure, unit-tested). */
#ifndef BX_SUSPEND_H
#define BX_SUSPEND_H
#include <stdint.h>

struct bx_sleep_sample {
    uint64_t sleep_ns;  /* clock counting suspend minus clock that stops in it */
    uint64_t attempts;  /* suspend_stats success + fail; 0 where unavailable */
};

/* A suspend, or any attempt (which freezes user space, e.g. pm_test=freezer),
 * happened between the samples. Clock-read jitter below 1 ms is ignored. */
static inline int bx_suspended(const struct bx_sleep_sample *prev,
                               const struct bx_sleep_sample *cur, uint64_t *slept_ns)
{
    uint64_t gap = cur->sleep_ns > prev->sleep_ns ? cur->sleep_ns - prev->sleep_ns : 0;
    *slept_ns = gap;
    return gap >= 1000000U || cur->attempts != prev->attempts;
}
#endif
