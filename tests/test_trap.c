/* SPDX-License-Identifier: GPL-2.0-or-later */
#if defined(__linux__)
#define _GNU_SOURCE
#else
#define _DARWIN_C_SOURCE
#endif
#include "bitoxin_core.h"
#include <assert.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

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

static int outcome(void (*body)(void))
{
    int status;
    pid_t pid = fork();
    if (pid == 0) { body(); _exit(0); }
    assert(pid > 0 && waitpid(pid, &status, 0) == pid);
    return WIFSIGNALED(status) ? WTERMSIG(status) : -WEXITSTATUS(status);
}

int main(void)
{
    if (!strcmp(bx_backend_name(), "portable-c")) {
        puts("SKIP in-place traps need a native lane");
        return 0;
    }
    assert(outcome(clean) == 0);
    assert(outcome(memory) == SIGTRAP);
    assert(outcome(data) == SIGTRAP);
    assert(outcome(state) == SIGTRAP);
    assert(outcome(released) == SIGTRAP);
    puts("PASS memory, data, state and released-buffer failures trap in place");
    return 0;
}
