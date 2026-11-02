/* SPDX-License-Identifier: GPL-2.0-or-later */
#if defined(__linux__)
#define _GNU_SOURCE
#else
#define _DARWIN_C_SOURCE
#endif
#include "bitoxin_core.h"
#include <assert.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#if defined(__linux__)
#include <ucontext.h>
#elif defined(__APPLE__)
#include <sys/ucontext.h>
#endif

#define TRAPPED 100 /* child exit status: TRAPPED + the kind register */
#define FOREIGN 99  /* SIGTRAP without the BITOXIN marker */
#define NO_HANDLER 98

static unsigned char buffer[64], other[64];

static struct bx_probe start(void)
{
    struct bx_probe p;
    assert(bx_init(&p, buffer, 64, 1) == BX_OK && bx_set_lane(&p, 1, 1) == BX_OK);
    return p;
}
static void clean(void) { struct bx_probe p = start(); while (p.passes < 2) bx_run(&p, 4096); }
static void memory(void) { struct bx_probe p = start(); buffer[34] &= 0xfe; bx_run(&p, 1); }
static void data(void) { struct bx_probe p = start(); bx_run(&p, 512); buffer[3] ^= 1; bx_run(&p, 64); }
static void state(void) { struct bx_probe p = start(); p.walked = 999; bx_run(&p, 1); }
static void released(void)
{
    struct bx_probe p = start();
    while (p.passes < 1) bx_run(&p, 4096);
    buffer[9] ^= 2;
    bx_rebind(&p, other);
}

/* The pc and the kind register (x2 / a2) at the trap, as the runner reads them. */
static uint64_t trap_kind(void *ctx, uint64_t *pc)
{
    ucontext_t *uc = ctx;
    int n = bx_trap_regno(BX_TRAP_REG_KIND);
#if defined(__linux__) && defined(__aarch64__)
    *pc = uc->uc_mcontext.pc;
    return uc->uc_mcontext.regs[n];
#elif defined(__linux__) && defined(__riscv)
    *pc = uc->uc_mcontext.__gregs[0];
    return uc->uc_mcontext.__gregs[n];
#elif defined(__APPLE__) && defined(__aarch64__)
    *pc = uc->uc_mcontext->__ss.__pc;
    return uc->uc_mcontext->__ss.__x[n];
#else
    (void)uc; (void)n;
    *pc = 0;
    return 0;
#endif
}

/* Exit with the kind instead of dying: no core dump or macOS crash report. */
static void caught(int sig, siginfo_t *info, void *ctx)
{
    uint64_t pc, kind = trap_kind(ctx, &pc);
    uint32_t marker = 0;
    (void)sig; (void)info;
    if (pc) memcpy(&marker, (const void *)(uintptr_t)(pc + 4U), sizeof(marker));
    _exit(marker == BX_TRAP_MARKER && kind < 16 ? TRAPPED + (int)kind : FOREIGN);
}

static int outcome(void (*body)(void))
{
    int status;
    pid_t pid = fork();
    if (pid == 0) {
        struct sigaction action;
        memset(&action, 0, sizeof(action));
        action.sa_sigaction = caught;
        action.sa_flags = SA_SIGINFO;
        sigemptyset(&action.sa_mask);
        if (sigaction(SIGTRAP, &action, NULL)) _exit(NO_HANDLER);
        body();
        _exit(0);
    }
    assert(pid > 0 && waitpid(pid, &status, 0) == pid);
    return WIFSIGNALED(status) ? WTERMSIG(status) : -WEXITSTATUS(status);
}

static int trapped(enum bx_lane_status kind) { return -(TRAPPED + (int)kind); }

int main(void)
{
    if (!strcmp(bx_backend_name(), "portable-c")) {
        puts("SKIP in-place traps need a native lane");
        return 0;
    }
    assert(outcome(clean) == 0);
    assert(outcome(memory) == trapped(BX_LANE_MEMORY));
    assert(outcome(data) == trapped(BX_LANE_DATA));
    assert(outcome(state) == trapped(BX_LANE_STATE));
    assert(outcome(released) == trapped(BX_LANE_DATA));
    puts("PASS memory, data, state and released-buffer failures trap in place by kind");
    return 0;
}
