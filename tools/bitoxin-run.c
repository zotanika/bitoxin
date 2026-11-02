/* SPDX-License-Identifier: GPL-2.0-or-later */
#if defined(__linux__)
#define _GNU_SOURCE
#else
#define _DARWIN_C_SOURCE
#endif
#include "bitoxin_core.h"
#include "bx_suspend.h"
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>
#if defined(__linux__)
#include <ucontext.h>
#elif defined(__APPLE__)
#include <sys/ucontext.h>
#endif

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal flag must be lock-free");
static atomic_int interrupted, abort_run, active;
static unsigned nthreads = 1, kib = 1024, seed = 1, chunk = 4096, pause_ms, rounds = 1;
static int churn, trap_mode, per_cpu;
static uint64_t suspends, suspended_ms;
static atomic_uint suspend_gen;
static int homes[32];
static uint64_t passes = 2;
struct worker {
    pthread_t thread;
    struct bx_probe probe;
    unsigned char *buffer;
    size_t size;
    unsigned id;
    int home_cpu, cpu;
    unsigned seen_gen;
    uint64_t churns, churn_failures, cpu_changes;
};
/* The worker running on this thread, for the SIGTRAP decoder. */
static _Thread_local struct worker *self;

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
 * while other threads run in the same address space. The next buffer is mapped
 * before the old one is released. A failed map or a refused rebind counts as a
 * churn failure and the run goes on; corruption found by the rebind is recorded
 * in the probe and returned. */
static int rebind_buffer(struct worker *w)
{
    unsigned char *next = map_buffer(w->size);
    if (!next) { ++w->churn_failures; return BX_OK; }
    if (bx_rebind(&w->probe, next) != BX_OK) {
        munmap(next, w->size);
        if (w->probe.error.code != BX_OK) return w->probe.error.code;
        ++w->churn_failures;
        return BX_OK;
    }
    munmap(w->buffer, w->size);
    w->buffer = next;
    ++w->churns;
    return BX_OK;
}

#if defined(__linux__) || defined(__APPLE__)
static uint64_t clock_ns(clockid_t id)
{
    struct timespec t;
    clock_gettime(id, &t);
    return (uint64_t)t.tv_sec * 1000000000U + (uint64_t)t.tv_nsec;
}

/* `counts` minus `stops`, where `stops` is the clock that stops in suspend.
 * Reading `stops` first keeps each difference at or above the true offset, so
 * it never wraps below zero; the smallest of three tries drops a pair of reads
 * split by preemption, which would otherwise look like a short suspend. */
static uint64_t sleep_offset(clockid_t counts, clockid_t stops)
{
    uint64_t best = UINT64_MAX;
    int i;
    for (i = 0; i < 3; ++i) {
        uint64_t before = clock_ns(stops);
        uint64_t gap = clock_ns(counts) - before;
        if (gap < best) best = gap;
    }
    return best;
}
#endif

#if defined(__linux__)
/* Leaves *value unchanged when the counter cannot be read. */
static void read_counter(const char *path, uint64_t *value)
{
    char text[32], *end;
    unsigned long long v;
    ssize_t n;
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return;
    n = read(fd, text, sizeof(text) - 1);
    close(fd);
    if (n <= 0) return;
    text[n] = 0;
    errno = 0;
    v = strtoull(text, &end, 10);
    if (!errno && end != text) *value = (uint64_t)v;
}
#endif

/* Monitor thread only. A counter that cannot be read keeps its last value (0
 * until the first good read; absent in containers: always 0), so a transient
 * read failure adds no suspend and no audit. Only a failure on the very first
 * sample costs one extra suspend and audit, when the counter is first read. */
static void sample(struct bx_sleep_sample *s)
{
#if defined(__linux__)
    static uint64_t successes, failures;
    s->sleep_ns = sleep_offset(CLOCK_BOOTTIME, CLOCK_MONOTONIC);
    read_counter("/sys/power/suspend_stats/success", &successes);
    read_counter("/sys/power/suspend_stats/fail", &failures);
    s->attempts = successes + failures;
#elif defined(__APPLE__)
    s->sleep_ns = sleep_offset(CLOCK_MONOTONIC_RAW, CLOCK_UPTIME_RAW);
    s->attempts = 0;
#else
    s->sleep_ns = 0;
    s->attempts = 0;
#endif
}

#if defined(__linux__)
static void pin_home(const struct worker *w)
{
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(w->home_cpu, &set);
    /* EINVAL while the home CPU is offline: ignored, track_cpu retries. */
    (void)pthread_setaffinity_np(pthread_self(), sizeof(set), &set);
}
#endif

/* Counts moves between CPUs after the baseline taken at worker start. A pinned
 * per-CPU worker moves only when it loses its affinity (home CPU offlined); it
 * is pinned back once the CPU returns, so one hotplug cycle counts 2 (off home,
 * back home) plus any moves while the home CPU is offline. Under a cgroup-v1
 * cpuset an offlined CPU may never come back to the set: the worker then stays
 * elsewhere, visible as cpu != home_cpu. */
static void track_cpu(struct worker *w)
{
#if defined(__linux__)
    int cpu = sched_getcpu();
    if (cpu >= 0 && w->cpu >= 0 && cpu != w->cpu) ++w->cpu_changes;
    if (cpu >= 0) w->cpu = cpu;
    if (per_cpu && cpu != w->home_cpu) {
        pin_home(w);
        cpu = sched_getcpu();
        if (cpu >= 0 && cpu != w->cpu) { ++w->cpu_changes; w->cpu = cpu; }
    }
#else
    (void)w;
#endif
}

/* Audit the retained state after a suspend or attempt. Once the suspend has
 * been detected this runs before a churn releases the buffer: at a pass
 * boundary the audit rechecks all of it. A suspend not yet detected at that
 * point is covered by bx_rebind, which checks the released buffer itself. */
static int audit_after_suspend(struct worker *w)
{
    unsigned gen = atomic_load(&suspend_gen);
    if (gen == w->seen_gen) return BX_OK;
    w->seen_gen = gen;
    return bx_audit(&w->probe);
}

/* seen_gen starts at 0 (calloc), the generation of the monitor's first sample
 * taken before setup, so a suspend during setup is audited. */
static void *run_worker(void *arg)
{
    struct worker *w = arg;
    self = w;
#if defined(__linux__)
    if (per_cpu) pin_home(w);
    w->cpu = sched_getcpu();   /* uncounted baseline: the start CPU is not a move */
#endif
    while (!atomic_load(&interrupted) && !atomic_load(&abort_run) &&
           (!passes || w->probe.passes < passes)) {
        uint64_t before = w->probe.passes;
        if (bx_run(&w->probe, chunk) != BX_OK || audit_after_suspend(w) != BX_OK ||
            (churn && w->probe.passes != before && (!passes || w->probe.passes < passes) &&
             rebind_buffer(w) != BX_OK)) {
            atomic_store(&abort_run, 1);
            break;
        }
        track_cpu(w);
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

/* Register access from a signal context. Local copies of the kernel layouts
 * avoid header conflicts between glibc and <asm/sigcontext.h>. */
#if defined(__linux__) && defined(__aarch64__)
struct bx_a64_ctx { uint32_t magic, size; };
struct bx_a64_fpsimd { struct bx_a64_ctx head; uint32_t fpsr, fpcr; uint64_t vregs[64]; };
#define BX_FPSIMD_MAGIC 0x46508001U
#endif
#if defined(__aarch64__)
#define BX_TRAP_INSN 0xd42162e0U /* brk #0xb17 */
#else
#define BX_TRAP_INSN 0x00100073U /* ebreak, 4-byte form */
#endif

static uint64_t ctx_pc(void *ctx)
{
    ucontext_t *uc = ctx;
#if defined(__linux__) && defined(__aarch64__)
    return uc->uc_mcontext.pc;
#elif defined(__linux__) && defined(__riscv)
    return uc->uc_mcontext.__gregs[0];
#elif defined(__APPLE__) && defined(__aarch64__)
    return uc->uc_mcontext->__ss.__pc;
#else
    (void)uc;
    return 0;
#endif
}

static uint64_t ctx_gpr(void *ctx, int n)
{
    ucontext_t *uc = ctx;
    if (n < 0 || n > 31) return 0;
#if defined(__linux__) && defined(__aarch64__)
    return n < 31 ? uc->uc_mcontext.regs[n] : 0;
#elif defined(__linux__) && defined(__riscv)
    return n ? uc->uc_mcontext.__gregs[n] : 0; /* __gregs[0] is the pc */
#elif defined(__APPLE__) && defined(__aarch64__)
    return n < 29 ? uc->uc_mcontext->__ss.__x[n] : 0;
#else
    (void)uc;
    return 0;
#endif
}

/* Half 0: low 64 bits, half 1: high 64 bits (none on RISC-V F). */
static uint64_t ctx_fpr(void *ctx, int n, unsigned half)
{
    ucontext_t *uc = ctx;
    uint64_t v = 0;
    if (n < 0 || n > 31 || half > 1) return 0;
#if defined(__linux__) && defined(__aarch64__)
    {
        /* Records in __reserved, each { magic, size }; FPSIMD comes first. */
        const unsigned char *rec = uc->uc_mcontext.__reserved;
        size_t at = 0, room = sizeof(uc->uc_mcontext.__reserved);
        struct bx_a64_ctx head;
        while (at + sizeof(head) <= room) {
            memcpy(&head, rec + at, sizeof(head));
            if (!head.magic || head.size < sizeof(head) || head.size > room - at) break;
            if (head.magic == BX_FPSIMD_MAGIC) {
                if (head.size >= sizeof(struct bx_a64_fpsimd))
                    memcpy(&v, rec + at + offsetof(struct bx_a64_fpsimd, vregs) +
                           (2U * (unsigned)n + half) * sizeof(v), sizeof(v));
                break;
            }
            at += head.size;
        }
    }
#elif defined(__linux__) && defined(__riscv)
    if (!half) v = uc->uc_mcontext.__fpregs.__d.__f[n];
#elif defined(__APPLE__) && defined(__aarch64__)
    {
        uint64_t parts[2];
        memcpy(parts, &uc->uc_mcontext->__ns.__v[n], sizeof(parts));
        v = parts[half];
    }
#else
    (void)uc;
#endif
    return v;
}

/* Async-signal-safe JSON pieces: no stdio, no allocation. */
static size_t put_str(char *out, size_t at, const char *s)
{
    while (*s && at < 1000) out[at++] = *s++;
    return at;
}

static size_t put_hex(char *out, size_t at, uint64_t v)
{
    int shift;
    out[at++] = '"';
    for (shift = 60; shift >= 0; shift -= 4) out[at++] = "0123456789abcdef"[(v >> shift) & 15U];
    out[at++] = '"';
    return at;
}

static size_t put_dec(char *out, size_t at, uint64_t v)
{
    char digits[24];
    int n = 0;
    do { digits[n++] = (char)('0' + v % 10U); v /= 10U; } while (v);
    while (n) out[at++] = digits[--n];
    return at;
}

/* --trap: decode the live registers at a BITOXIN trap, print one JSON record
 * and exit 1. Async-signal-safe: no stdio, no allocation; only mem*, the pure
 * decoders, write and _exit (sigaction and raise for a foreign trap, which
 * keeps its default action). A trap is ours when the trap instruction is
 * followed by the marker word, both read with memcpy (on RISC-V they may be
 * only 2-byte aligned). Lane traps (kinds 1, 2, 5): A = token, C = check word,
 * bit = the visited bit. C-detected traps (kinds 3, 4): A = expected,
 * B = observed, C = bit. */
static void trap_signal(int sig, siginfo_t *info, void *ctx)
{
    static const char *const kinds[] = { "none", "register", "memory", "data", "state", "simd" };
    char out[1024];
    size_t at = 0;
    uint64_t pc = ctx_pc(ctx), kind, a, b, c, expected = 0, observed = 0;
    uint64_t regs[BX_SIMD_MAX * 2];
    uint32_t words[2] = { 0, 0 };
    int i, index;
    const char *reg = "";
    (void)sig; (void)info;
    if (pc) memcpy(words, (const void *)(uintptr_t)pc, sizeof(words));
    if (words[0] != BX_TRAP_INSN || words[1] != BX_TRAP_MARKER || !self) {
        /* Not ours: take the default action. SA_RESETHAND is not enough, as
         * POSIX lets SIGTRAP keep its handler (macOS does); the raised signal
         * stays blocked until the handler returns. */
        struct sigaction fallback;
        memset(&fallback, 0, sizeof(fallback));
        fallback.sa_handler = SIG_DFL;
        sigemptyset(&fallback.sa_mask);
        (void)sigaction(SIGTRAP, &fallback, NULL);
        (void)raise(SIGTRAP);
        return;
    }
    kind = ctx_gpr(ctx, bx_trap_regno(BX_TRAP_REG_KIND));
    a = ctx_gpr(ctx, bx_trap_regno(BX_TRAP_REG_A));
    b = ctx_gpr(ctx, bx_trap_regno(BX_TRAP_REG_B));
    c = ctx_gpr(ctx, bx_trap_regno(BX_TRAP_REG_C));
    if (kind == BX_LANE_REGISTER) {
        for (i = 0; i < bx_lane_count(); ++i) regs[i] = ctx_gpr(ctx, bx_lane_regno(i));
        index = bx_lane_decode(a, regs, &expected, &observed);
        reg = bx_lane_reg_name(index);
#ifdef BX_SIMD
    } else if (kind == BX_LANE_SIMD) {
        for (i = 0; i < BX_SIMD_MAX; ++i) {
            regs[2 * i] = ctx_fpr(ctx, bx_simd_regno(i), 0);
            regs[2 * i + 1] = ctx_fpr(ctx, bx_simd_regno(i), 1);
        }
        index = bx_simd_decode(a, regs, &expected, &observed);
        reg = bx_simd_reg_name(index);
#endif
    }
    at = put_str(out, at, "{\"schema\":2,\"status\":\"trapped\",\"kind\":\"");
    at = put_str(out, at, kind <= 5 ? kinds[kind] : "unknown");
    at = put_str(out, at, "\",\"worker\":");
    at = put_dec(out, at, self->id);
    at = put_str(out, at, ",\"pass\":");
    at = put_dec(out, at, self->probe.passes);
    at = put_str(out, at, ",\"bit\":");
    at = put_dec(out, at, kind == BX_LANE_DATA || kind == BX_LANE_STATE ? c : self->probe.cursor);
    at = put_str(out, at, ",\"a\":");
    at = put_hex(out, at, a);
    at = put_str(out, at, ",\"b\":");
    at = put_hex(out, at, b);
    at = put_str(out, at, ",\"c\":");
    at = put_hex(out, at, c);
    at = put_str(out, at, ",\"lane_reg\":\"");
    at = put_str(out, at, reg);
    at = put_str(out, at, "\",\"lane_expected\":");
    at = put_hex(out, at, expected);
    at = put_str(out, at, ",\"lane_observed\":");
    at = put_hex(out, at, observed);
    at = put_str(out, at, "}\n");
    (void)!write(STDOUT_FILENO, out, at);
    _exit(1);
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
               "            [--pause-ms N] [--lane-rounds N] [--churn] [--per-cpu] [--trap]\n"
               "Defaults: 1024 KiB/worker, 1 worker, 2 passes, seed 1, chunk 4096,\n"
               "no pause, 1 lane round.\n"
               "--kib 0 picks the largest power of two per worker, up to 256 MiB in total,\n"
               "that the address space accepts. It is not a free-RAM check: under\n"
               "overcommit or a cgroup memory limit the fill can be OOM-killed.\n"
               "--churn maps each new buffer before releasing the old one, so peak memory\n"
               "is up to twice the buffer total.\n"
               "--per-cpu replaces --threads with one worker per allowed CPU (at most 32),\n"
               "each kept on its CPU (Linux only).\n"
               "--trap stops at the first failure with a trap in place (brk/ebreak) and\n"
               "prints one JSON record decoded from the live registers instead (exit 1).\n"
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
    struct bx_sleep_sample prev, cur;
    unsigned i, created = 0, allocated = 0;
    int setup_error = 0, failed, result, a;
    const char *status;
    for (a = 1; a < argc; ++a) {
        uint64_t value;
        const char *name = argv[a];
        if (!strcmp(name, "--help")) { usage(stdout); return 0; }
        if (!strcmp(name, "--churn")) { churn = 1; continue; }
        if (!strcmp(name, "--per-cpu")) { per_cpu = 1; continue; }
        if (!strcmp(name, "--trap")) { trap_mode = 1; continue; }
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
    if (per_cpu) {
#if defined(__linux__)
        cpu_set_t allowed;
        int c;
        if (sched_getaffinity(0, sizeof(allowed), &allowed)) { perror("sched_getaffinity"); return 3; }
        nthreads = 0;
        for (c = 0; c < CPU_SETSIZE && nthreads < 32; ++c)
            if (CPU_ISSET(c, &allowed)) homes[nthreads++] = c;
#else
        fprintf(stderr, "--per-cpu is supported on Linux only.\n");
        return 2;
#endif
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
    if (trap_mode) {
        struct sigaction trap_action;
        memset(&trap_action, 0, sizeof(trap_action));
        trap_action.sa_sigaction = trap_signal;
        trap_action.sa_flags = SA_SIGINFO | SA_RESETHAND;
        sigemptyset(&trap_action.sa_mask);
        if (sigaction(SIGTRAP, &trap_action, NULL)) { perror("sigaction"); return 3; }
    }
    workers = calloc(nthreads, sizeof(*workers));
    if (!workers) { perror("calloc"); return 3; }
    clock_gettime(CLOCK_MONOTONIC, &start);
    if (allocate(workers, &allocated)) {
        setup_error = 1;
    } else if (seed >= kib * 8192U) { /* only reachable with --kib 0 */
        for (i = 0; i < allocated; ++i) munmap(workers[i].buffer, workers[i].size);
        free(workers);
        fprintf(stderr, "--kib 0 chose %u KiB per worker; --seed must be below %u.\n",
                kib, kib * 8192U);
        goto bad_args;
    }
    sample(&prev);   /* before any probe state exists: see run_worker */
    for (i = 0; !setup_error && i < nthreads; ++i) {
        unsigned s = 1U + ((seed - 1U + i) % (kib * 8192U - 1U));
        workers[i].id = i;
        workers[i].home_cpu = per_cpu ? homes[i] : -1;
        workers[i].cpu = -1;
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
    /* The last tick can count a suspend after every worker has exited, so a run
     * can end with suspends >= 1 and audits 0. */
    while (atomic_load(&active) > 0) {
        struct timespec tick = { 0, 50L * 1000000L };
        uint64_t slept;
        (void)nanosleep(&tick, NULL);
        sample(&cur);
        if (bx_suspended(&prev, &cur, &slept)) {
            ++suspends;
            suspended_ms += slept / 1000000U;
            atomic_fetch_add(&suspend_gen, 1);
        }
        prev = cur;
    }
    for (i = 0; i < created; ++i) pthread_join(workers[i].thread, NULL);
    clock_gettime(CLOCK_MONOTONIC, &end);
    /* A recorded probe error wins over setup failure and interruption. */
    failed = !setup_error && atomic_load(&abort_run);
    for (i = 0; i < created; ++i)
        if (workers[i].probe.error.code != BX_OK) failed = 1;
    result = failed ? 1 : setup_error ? 3 : atomic_load(&interrupted) ? 130 : 0;
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
