/* SPDX-License-Identifier: GPL-2.0-or-later */
#define _POSIX_C_SOURCE 200809L
#include "bitoxin_core.h"
#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal flag must be lock-free");
static atomic_int interrupted, abort_run;
static unsigned nthreads = 1, kib = 1024, seed = 1, chunk = 4096, pause_ms;
static uint64_t passes = 2;
struct worker { pthread_t thread; struct bx_probe probe; unsigned char *buffer; };

static void stop_signal(int sig)
{
    (void)sig;
    atomic_store_explicit(&interrupted, 1, memory_order_relaxed);
}

static void *run_worker(void *arg)
{
    struct worker *w = arg;
    while (!atomic_load(&interrupted) && !atomic_load(&abort_run) &&
           (!passes || w->probe.passes < passes)) {
        if (bx_run(&w->probe, chunk) != BX_OK) {
            atomic_store(&abort_run, 1);
            break;
        }
        if (pause_ms) {
            struct timespec delay = { pause_ms / 1000, (long)(pause_ms % 1000) * 1000000L };
            (void)nanosleep(&delay, NULL);
        } else {
            sched_yield();
        }
    }
    return NULL;
}

static int number(const char *s, uint64_t *out)
{
    char *end;
    unsigned long long v;
    if (!s[0] || s[0] < '0' || s[0] > '9') return 0;
    errno = 0;
    v = strtoull(s, &end, 10);
    if (errno || *end) return 0;
    *out = (uint64_t)v;
    return 1;
}

static void usage(FILE *f)
{
    fprintf(f, "bitoxin-run [--kib N] [--threads N] [--passes N] [--seed N] "
               "[--chunk N] [--pause-ms N]\n"
               "Defaults: 1024 KiB/worker, 1 worker, 2 passes, seed 1, chunk 4096, no pause.\n"
               "--passes 0 runs until SIGINT/SIGTERM. Output: one final JSON record.\n");
}

int main(int argc, char **argv)
{
    struct worker *workers;
    struct sigaction action;
    struct timespec start, end;
    unsigned i, created = 0, allocated = 0;
    int setup_error = 0, result;
    const char *status;
    for (int a = 1; a < argc; a += 2) {
        uint64_t value;
        if (!strcmp(argv[a], "--help")) { usage(stdout); return 0; }
        if (a + 1 == argc || !number(argv[a + 1], &value)) goto bad_args;
        if (!strcmp(argv[a], "--passes")) { passes = value; continue; }
        if (value > UINT32_MAX) goto bad_args;
        if (!strcmp(argv[a], "--kib")) kib = (unsigned)value;
        else if (!strcmp(argv[a], "--threads")) nthreads = (unsigned)value;
        else if (!strcmp(argv[a], "--seed")) seed = (unsigned)value;
        else if (!strcmp(argv[a], "--chunk")) chunk = (unsigned)value;
        else if (!strcmp(argv[a], "--pause-ms")) pause_ms = (unsigned)value;
        else goto bad_args;
    }
    if (!kib || kib > BX_MAX_BYTES / 1024 || (kib & (kib - 1)) ||
        !nthreads || nthreads > 32 || (uint64_t)kib * nthreads > 256U * 1024U ||
        !seed || seed >= kib * 8192U || !chunk || chunk > 65536 || pause_ms > 1000)
        goto bad_args;
    memset(&action, 0, sizeof(action));
    action.sa_handler = stop_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGINT, &action, NULL) || sigaction(SIGTERM, &action, NULL)) {
        perror("sigaction"); return 3;
    }
    workers = calloc(nthreads, sizeof(*workers));
    if (!workers) { perror("calloc"); return 3; }
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (i = 0; i < nthreads; ++i) {
        unsigned s = 1U + ((seed - 1U + i) % (kib * 8192U - 1U));
        workers[i].buffer = malloc((size_t)kib * 1024U);
        if (!workers[i].buffer) { setup_error = 1; break; }
        ++allocated;
        if (bx_init(&workers[i].probe, workers[i].buffer, kib * 1024U, s) != BX_OK) {
            setup_error = 1; break;
        }
    }
    if (!setup_error) {
        for (i = 0; i < nthreads; ++i) {
            int err = pthread_create(&workers[i].thread, NULL, run_worker, &workers[i]);
            if (err) { fprintf(stderr, "pthread_create: %s\n", strerror(err)); setup_error = 1; break; }
            ++created;
        }
    }
    if (setup_error) atomic_store(&abort_run, 1);
    for (i = 0; i < created; ++i) pthread_join(workers[i].thread, NULL);
    clock_gettime(CLOCK_MONOTONIC, &end);
    result = setup_error ? 3 : atomic_load(&abort_run) ? 1 : atomic_load(&interrupted) ? 130 : 0;
    status = result == 3 ? "setup_failed" : result == 1 ? "failed" : result == 130 ? "interrupted" : "complete";
    printf("{\"schema\":1,\"status\":\"%s\",\"backend\":\"%s\",\"kib_per_worker\":%u,"
           "\"requested_passes\":%" PRIu64 ",\"chunk\":%u,\"pause_ms\":%u,"
           "\"elapsed_monotonic_seconds\":%.6f,\"workers\":[",
           status, bx_backend_name(), kib, passes, chunk, pause_ms,
           (double)(end.tv_sec - start.tv_sec) + (double)(end.tv_nsec - start.tv_nsec) / 1e9);
    for (i = 0; i < created; ++i) {
        struct bx_probe *p = &workers[i].probe;
        printf("%s{\"id\":%u,\"seed\":%u,\"passes\":%" PRIu64 ",\"operations\":%" PRIu64
               ",\"phase\":\"%s\",\"walked\":%u,\"verified\":%u,\"error\":\"%s\","
               "\"error_bit\":%u,\"expected\":\"%016" PRIx64 "\",\"observed\":\"%016" PRIx64 "\"}",
               i ? "," : "", i, p->seed, p->passes, p->operations,
               p->phase == BX_WALK ? "walk" : "verify", p->walked, p->verified,
               bx_result_name(p->error.code), p->error.bit, p->error.expected, p->error.observed);
    }
    puts("]}");
    for (i = 0; i < allocated; ++i) free(workers[i].buffer);
    free(workers);
    return result;
bad_args:
    usage(stderr);
    fprintf(stderr, "Invalid configuration (power-of-two KiB; total <= 256 MiB).\n");
    return 2;
}
