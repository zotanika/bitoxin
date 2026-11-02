/* SPDX-License-Identifier: GPL-2.0-or-later */
#if defined(__linux__)
#define _GNU_SOURCE
#else
#define _DARWIN_C_SOURCE
#endif
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
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal flag must be lock-free");
static atomic_int interrupted, abort_run, active;
static unsigned nthreads = 1, kib = 1024, seed = 1, chunk = 4096, pause_ms, rounds = 1;
static int churn;
/* Filled by Tasks 10-11 (--trap, --per-cpu, suspend detection). */
static int trap_mode, per_cpu;
static uint64_t suspends, suspended_ms;
static uint64_t passes = 2;
struct worker {
    pthread_t thread;
    struct bx_probe probe;
    unsigned char *buffer;
    size_t size;
    unsigned id;
    int home_cpu, cpu;
    uint64_t churns, churn_failures, cpu_changes;
};

static void stop_signal(int sig)
{
    (void)sig;
    atomic_store_explicit(&interrupted, 1, memory_order_relaxed);
}

static unsigned char *map_buffer(size_t size)
{
    void *p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    return p == MAP_FAILED ? NULL : p;
}

/* Fresh pages at each verified boundary: page-table teardown and TLB shootdowns
 * while other threads run in the same address space. */
static void rebind_buffer(struct worker *w)
{
    unsigned char *next = map_buffer(w->size);
    if (!next) { ++w->churn_failures; return; }
    if (bx_rebind(&w->probe, next) != BX_OK) {
        munmap(next, w->size);
        ++w->churn_failures;
        return;
    }
    munmap(w->buffer, w->size);
    w->buffer = next;
    ++w->churns;
}

static void *run_worker(void *arg)
{
    struct worker *w = arg;
    while (!atomic_load(&interrupted) && !atomic_load(&abort_run) &&
           (!passes || w->probe.passes < passes)) {
        uint64_t before = w->probe.passes;
        if (bx_run(&w->probe, chunk) != BX_OK) {
            atomic_store(&abort_run, 1);
            break;
        }
        if (churn && w->probe.passes != before && (!passes || w->probe.passes < passes))
            rebind_buffer(w);
        /* BITOXIN_WORKER_HOOK: Task 10 adds suspend audits and CPU tracking here. */
        if (pause_ms) {
            struct timespec delay = { pause_ms / 1000, (long)(pause_ms % 1000) * 1000000L };
            (void)nanosleep(&delay, NULL);
        } else {
            sched_yield();
        }
    }
    atomic_fetch_sub(&active, 1);
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
    fprintf(f, "bitoxin-run [--kib N] [--threads N] [--passes N] [--seed N] [--chunk N]\n"
               "            [--pause-ms N] [--lane-rounds N] [--churn]\n"
               "Defaults: 1024 KiB/worker (0 = largest that maps), 1 worker, 2 passes,\n"
               "seed 1, chunk 4096, no pause, 1 lane round.\n"
               "--passes 0 runs until SIGINT/SIGTERM. Output: one final JSON record.\n");
}

/* Largest power-of-two KiB per worker within the 256 MiB total that maps. */
static int allocate(struct worker *workers, unsigned *allocated)
{
    unsigned want = kib, i;
    if (!want) {
        want = BX_MAX_BYTES / 1024;
        while ((uint64_t)want * nthreads > 256U * 1024U) want >>= 1;
    }
    for (;;) {
        for (i = 0; i < nthreads; ++i) {
            workers[i].size = (size_t)want * 1024U;
            workers[i].buffer = map_buffer(workers[i].size);
            if (!workers[i].buffer) break;
        }
        if (i == nthreads) { kib = want; *allocated = i; return 0; }
        while (i--) munmap(workers[i].buffer, workers[i].size);
        if (kib || want == 1) { *allocated = 0; return -1; }
        want >>= 1;
    }
}

static void print_worker(const struct worker *w, int first)
{
    const struct bx_probe *p = &w->probe;
    const struct bx_error *e = &p->error;
    const char *reg = e->lane_index < 0 ? "" :
#ifdef BX_SIMD
        e->lane_simd ? bx_simd_reg_name(e->lane_index) :
#endif
        bx_lane_reg_name(e->lane_index);
    printf("%s{\"id\":%u,\"seed\":%u,\"home_cpu\":%d,\"cpu\":%d,\"cpu_changes\":%" PRIu64
           ",\"churns\":%" PRIu64 ",\"churn_failures\":%" PRIu64 ",\"audits\":%" PRIu64
           ",\"passes\":%" PRIu64 ",\"operations\":%" PRIu64 ",\"phase\":\"%s\","
           "\"walked\":%u,\"verified\":%u,\"error\":\"%s\",\"error_bit\":%u,"
           "\"expected\":\"%016" PRIx64 "\",\"observed\":\"%016" PRIx64 "\","
           "\"lane_reg\":\"%s\",\"lane_expected\":\"%016" PRIx64 "\","
           "\"lane_observed\":\"%016" PRIx64 "\"}",
           first ? "" : ",", w->id, p->seed, w->home_cpu, w->cpu, w->cpu_changes,
           w->churns, w->churn_failures, p->audits, p->passes, p->operations,
           p->phase == BX_WALK ? "walk" : "verify", p->walked, p->verified,
           bx_result_name(e->code), e->bit, e->expected, e->observed, reg,
           e->lane_expected, e->lane_observed);
}

int main(int argc, char **argv)
{
    struct worker *workers;
    struct sigaction action;
    struct timespec start, end;
    unsigned i, created = 0, allocated = 0;
    int setup_error = 0, result, a;
    const char *status;
    for (a = 1; a < argc; ++a) {
        uint64_t value;
        const char *name = argv[a];
        if (!strcmp(name, "--help")) { usage(stdout); return 0; }
        if (!strcmp(name, "--churn")) { churn = 1; continue; }
        /* BITOXIN_FLAG_HOOK: Tasks 10-11 add --per-cpu and --trap here. */
        if (a + 1 == argc || !number(argv[++a], &value)) goto bad_args;
        if (!strcmp(name, "--passes")) { passes = value; continue; }
        if (value > UINT32_MAX) goto bad_args;
        if (!strcmp(name, "--kib")) kib = (unsigned)value;
        else if (!strcmp(name, "--threads")) nthreads = (unsigned)value;
        else if (!strcmp(name, "--seed")) seed = (unsigned)value;
        else if (!strcmp(name, "--chunk")) chunk = (unsigned)value;
        else if (!strcmp(name, "--pause-ms")) pause_ms = (unsigned)value;
        else if (!strcmp(name, "--lane-rounds")) rounds = (unsigned)value;
        else goto bad_args;
    }
    if (kib > BX_MAX_BYTES / 1024 || (kib & (kib - 1)) || !nthreads || nthreads > 32 ||
        (uint64_t)kib * nthreads > 256U * 1024U || !seed || (kib && seed >= kib * 8192U) ||
        !chunk || chunk > 65536 || pause_ms > 1000 || !rounds || rounds > BX_MAX_ROUNDS)
        goto bad_args;
    memset(&action, 0, sizeof(action));
    action.sa_handler = stop_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGINT, &action, NULL) || sigaction(SIGTERM, &action, NULL)) {
        perror("sigaction"); return 3;
    }
    /* BITOXIN_SETUP_HOOK: Task 11 installs the SIGTRAP decoder here. */
    workers = calloc(nthreads, sizeof(*workers));
    if (!workers) { perror("calloc"); return 3; }
    clock_gettime(CLOCK_MONOTONIC, &start);
    if (allocate(workers, &allocated)) {
        setup_error = 1;
    } else if (seed >= kib * 8192U) {
        for (i = 0; i < allocated; ++i) munmap(workers[i].buffer, workers[i].size);
        free(workers);
        goto bad_args;
    }
    for (i = 0; !setup_error && i < nthreads; ++i) {
        unsigned s = 1U + ((seed - 1U + i) % (kib * 8192U - 1U));
        workers[i].id = i;
        workers[i].home_cpu = workers[i].cpu = -1;
        if (bx_init(&workers[i].probe, workers[i].buffer, kib * 1024U, s) != BX_OK ||
            bx_set_lane(&workers[i].probe, rounds, trap_mode) != BX_OK)
            setup_error = 1;
    }
    for (i = 0; !setup_error && i < nthreads; ++i) {
        int err;
        atomic_fetch_add(&active, 1);
        err = pthread_create(&workers[i].thread, NULL, run_worker, &workers[i]);
        if (err) {
            atomic_fetch_sub(&active, 1);
            fprintf(stderr, "pthread_create: %s\n", strerror(err));
            setup_error = 1;
            break;
        }
        ++created;
    }
    if (setup_error) atomic_store(&abort_run, 1);
    /* BITOXIN_MONITOR_HOOK: Task 10 watches for suspend here while workers run. */
    for (i = 0; i < created; ++i) pthread_join(workers[i].thread, NULL);
    clock_gettime(CLOCK_MONOTONIC, &end);
    result = setup_error ? 3 : atomic_load(&abort_run) ? 1 : atomic_load(&interrupted) ? 130 : 0;
    status = result == 3 ? "setup_failed" : result == 1 ? "failed" :
             result == 130 ? "interrupted" : "complete";
    printf("{\"schema\":2,\"status\":\"%s\",\"backend\":\"%s\",\"kib_per_worker\":%u,"
           "\"requested_passes\":%" PRIu64 ",\"chunk\":%u,\"pause_ms\":%u,"
           "\"lane_rounds\":%u,\"trap\":%s,\"churn\":%s,\"per_cpu\":%s,"
           "\"suspends\":%" PRIu64 ",\"suspended_ms\":%" PRIu64 ","
           "\"elapsed_monotonic_seconds\":%.6f,\"workers\":[",
           status, bx_backend_name(), kib, passes, chunk, pause_ms, rounds,
           trap_mode ? "true" : "false", churn ? "true" : "false",
           per_cpu ? "true" : "false", suspends, suspended_ms,
           (double)(end.tv_sec - start.tv_sec) + (double)(end.tv_nsec - start.tv_nsec) / 1e9);
    for (i = 0; i < created; ++i) print_worker(&workers[i], i == 0);
    puts("]}");
    for (i = 0; i < allocated; ++i) munmap(workers[i].buffer, workers[i].size);
    free(workers);
    return result;
bad_args:
    usage(stderr);
    fprintf(stderr, "Invalid configuration (power-of-two KiB; total <= 256 MiB).\n");
    return 2;
}
