/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include "bitoxin_lane.h"
#ifdef __KERNEL__
#include <linux/string.h>
#else
#include <string.h>
#endif

static const char *const lane_names[BX_LANE_REGS] = BX_LANE_NAMES;
static const signed char lane_regnos[BX_LANE_REGS] = BX_LANE_REGNOS;
static const signed char trap_regnos[4] = BX_TRAP_REGNOS;
_Static_assert(BX_LANE_REGS <= BX_LANE_MAX, "lane snapshot too small");

/* Right-shift Galois masks, degrees 9..30; original lfsrtabs.h convention.
 * Degree 14 corrects the legacy 0x201d mask. Every mask's order is tested. */
static const bx_u32 taps[] = {
    0x110, 0x240, 0x500, 0x829, 0x100d, 0x3802, 0x6000, 0xd008,
    0x12000, 0x20040, 0x40023, 0x90000, 0x140000, 0x300000,
    0x420000, 0xe10000, 0x1200000, 0x2000023, 0x4000013,
    0x9000000, 0x14000000, 0x20000029
};

static bx_u32 mask_for(bx_u32 bytes)
{
    unsigned degree = 3;
    while (bytes > 1) { ++degree; bytes >>= 1; }
    return taps[degree - 9];
}

static int valid_size(bx_u32 bytes)
{
    return bytes >= BX_MIN_BYTES && bytes <= BX_MAX_BYTES &&
           (bytes & (bytes - 1)) == 0;
}

static int valid_state(const struct bx_probe *p)
{
    return p->buffer && valid_size(p->bytes) && p->bits == p->bytes * 8U &&
           p->taps == mask_for(p->bytes) && p->seed && p->seed < p->bits &&
           p->lfsr && p->lfsr < p->bits && p->expected <= 1 &&
           (p->phase == BX_WALK || p->phase == BX_VERIFY) &&
           p->walked <= p->bits && p->verified <= p->bytes &&
           !(p->phase == BX_WALK && p->verified != 0) &&
           p->rounds && p->rounds <= BX_MAX_ROUNDS && p->trap <= 1;
}

static int fail(struct bx_probe *p, enum bx_result code, bx_u32 bit,
                bx_u64 expected, bx_u64 observed)
{
    /* Lane failures trap inside the lane; these are detected in C. */
    if (p->trap && (code == BX_DATA_ERROR || code == BX_STATE_ERROR))
        bx_trap_now(code == BX_DATA_ERROR ? BX_LANE_DATA : BX_LANE_STATE,
                    expected, observed, bit);
    p->error.code = code;
    p->error.phase = p->phase;
    p->error.bit = bit;
    p->error.expected = expected;
    p->error.observed = observed;
    p->error.pass = p->passes;
    return code;
}

static int lane_fail(struct bx_probe *p, bx_u32 index, bx_u64 token, bx_u64 carried)
{
    p->error.lane_index = bx_lane_decode(token, p->lane_regs, &p->error.lane_expected,
                                         &p->error.lane_observed);
    p->error.lane_simd = 0;
    return fail(p, BX_REGISTER_ERROR, index, token, carried);
}

int bx_init(struct bx_probe *p, volatile bx_u8 *buffer, bx_u32 bytes, bx_u32 seed)
{
    bx_u32 i;
    if (!p) return BX_BAD_CONFIG;
    memset(p, 0, sizeof(*p));
    p->error.lane_index = -1;
    if (!buffer || !valid_size(bytes) || !seed || seed >= bytes * 8U) {
        p->error.code = BX_BAD_CONFIG;
        return BX_BAD_CONFIG;
    }
    p->buffer = buffer;
    p->bytes = bytes;
    p->bits = bytes * 8U;
    p->seed = seed;
    p->lfsr = seed;
    p->taps = mask_for(bytes);
    p->expected = 1;
    p->phase = BX_WALK;
    p->rounds = 1;
    for (i = 0; i < bytes; ++i) buffer[i] = 0xff;
    return BX_OK;
}

int bx_set_lane(struct bx_probe *p, bx_u32 rounds, int trap)
{
    if (!p || !rounds || rounds > BX_MAX_ROUNDS)
        return BX_BAD_CONFIG;
    p->rounds = rounds;
    p->trap = trap ? 1 : 0;
    return BX_OK;
}

int bx_run(struct bx_probe *p, bx_u32 budget)
{
    if (!p) return BX_BAD_CONFIG;
    if (p->error.code != BX_OK) return p->error.code;
    if (!valid_state(p))
        return fail(p, BX_STATE_ERROR, 0, 0, p->lfsr);

    while (budget--) {
        if (p->phase == BX_WALK) {
            bx_u32 index, lfsr, status, rounds;
            bx_u8 observed, mask;
            bx_u64 token, carried;
            if (p->walked >= p->bits)
                return fail(p, BX_STATE_ERROR, 0, p->bits - 1, p->walked);
            /* Traversal state is reloaded from memory every step (2018 design).
             * Zero rounds would never end the asm lane loops (AArch64, RISC-V). */
            rounds = *(volatile bx_u32 *)&p->rounds;
            if (!rounds || rounds > BX_MAX_ROUNDS)
                return fail(p, BX_STATE_ERROR, 0, BX_MAX_ROUNDS, rounds);
            lfsr = *(volatile bx_u32 *)&p->lfsr;
            if (p->walked == p->bits - 1) {
                if (lfsr != p->seed)
                    return fail(p, BX_STATE_ERROR, 0, p->seed, lfsr);
                index = 0; /* Zero is outside the LFSR cycle, inside the test. */
            } else {
                bx_u32 feedback = *(volatile bx_u32 *)&p->taps;
                lfsr = (lfsr >> 1) ^ ((0U - (lfsr & 1U)) & feedback);
                if (!lfsr || lfsr >= p->bits)
                    return fail(p, BX_STATE_ERROR, 0, p->bits, lfsr);
                *(volatile bx_u32 *)&p->lfsr = lfsr;
                index = lfsr;
            }
            *(volatile bx_u32 *)&p->cursor = index;
            observed = p->buffer[index >> 3];
            mask = (bx_u8)(1U << (index & 7U));
            /* Actual load in the low byte; varied upper bits exercise the GPRs.
             * The lane checks the bit and supplies the store. */
            token = (((bx_u64)index * 0x9e3779b97f4a7c15ULL) & ~0xffULL) | observed;
            carried = bx_lane(token, (index & 7U) | ((bx_u64)p->expected << 8),
                              rounds, p->trap ? NULL : p->lane_regs, &status);
            if (status == BX_LANE_MEMORY)
                return fail(p, BX_DATA_ERROR, index, p->expected, !p->expected);
            if (status != BX_LANE_OK)
                return lane_fail(p, index, token, carried);
            p->buffer[index >> 3] = (bx_u8)carried ^ mask;
            ++p->walked;
            ++p->operations;
            if (p->walked == p->bits) p->phase = BX_VERIFY;
        } else {
            bx_u8 want = p->expected ? 0 : 0xff;
            bx_u8 got;
            if (p->walked != p->bits || p->verified >= p->bytes)
                return fail(p, BX_STATE_ERROR, 0, p->bytes - 1, p->verified);
            got = p->buffer[p->verified];
            if (got != want)
                return fail(p, BX_DATA_ERROR, p->verified * 8U, want, got);
            ++p->verified;
            ++p->operations;
            if (p->verified == p->bytes) {
                ++p->passes;
                p->expected ^= 1U;
                p->walked = p->verified = 0;
                p->phase = BX_WALK;
                return BX_OK; /* Let caller enforce exact pass limits. */
            }
        }
    }
    return BX_OK;
}

static unsigned popcount8(bx_u8 v)
{
    unsigned n = 0;
    while (v) { v &= (bx_u8)(v - 1U); ++n; }
    return n;
}

/* Check the whole retained state without changing it. Replaying the walk proves
 * every visited bit is flipped; counting flipped bits then proves no unvisited
 * bit is. O(walked + bytes) time, no extra memory. */
int bx_audit(struct bx_probe *p)
{
    bx_u32 i, lfsr, flipped = 0;
    bx_u8 visited;
    if (!p) return BX_BAD_CONFIG;
    if (p->error.code != BX_OK) return p->error.code;
    if (!valid_state(p))
        return fail(p, BX_STATE_ERROR, 0, 0, p->lfsr);
    visited = p->expected ? 0U : 1U;
    if (p->phase == BX_VERIFY) {
        bx_u8 want = p->expected ? 0 : 0xff;
        for (i = 0; i < p->bytes; ++i) {
            bx_u8 got = p->buffer[i]; /* report the byte that was compared */
            if (got != want)
                return fail(p, BX_DATA_ERROR, i * 8U, want, got);
        }
    } else {
        lfsr = p->seed;
        for (i = 0; i < p->walked; ++i) { /* walked < bits here: no zero step */
            lfsr = (lfsr >> 1) ^ ((0U - (lfsr & 1U)) & p->taps);
            if (((p->buffer[lfsr >> 3] >> (lfsr & 7U)) & 1U) != visited)
                return fail(p, BX_DATA_ERROR, lfsr, visited, !visited);
        }
        if (lfsr != p->lfsr)
            return fail(p, BX_STATE_ERROR, 0, lfsr, p->lfsr);
        for (i = 0; i < p->bytes; ++i)
            flipped += popcount8(p->expected ? (bx_u8)~p->buffer[i] : p->buffer[i]);
        if (flipped != p->walked)
            return fail(p, BX_DATA_ERROR, BX_AUDIT_UNLOCATED, p->walked, flipped);
    }
    ++p->audits;
    return BX_OK;
}

const char *bx_result_name(enum bx_result code)
{
    switch (code) {
    case BX_OK: return "ok";
    case BX_BAD_CONFIG: return "bad_config";
    case BX_DATA_ERROR: return "data_error";
    case BX_REGISTER_ERROR: return "register_error";
    case BX_STATE_ERROR: return "state_error";
    default: return "unknown";
    }
}

const char *bx_backend_name(void)
{
    return BX_BACKEND_NAME;
}

int bx_lane_count(void)
{
    return BX_LANE_REGS;
}

const char *bx_lane_reg_name(int index)
{
    return index >= 0 && index < BX_LANE_REGS ? lane_names[index] : "";
}

int bx_lane_regno(int index)
{
    return index >= 0 && index < BX_LANE_REGS ? lane_regnos[index] : -1;
}

int bx_trap_regno(enum bx_trap_reg reg)
{
    return (unsigned)reg < 4U ? trap_regnos[reg] : -1;
}

int bx_lane_decode(bx_u64 token, const bx_u64 *regs, bx_u64 *expected, bx_u64 *observed)
{
    bx_u64 v = token;
    int k;
    for (k = 0; k < BX_LANE_REGS; ++k) {
        v = bx_lane_ref_step((unsigned)k, v);
        if (regs[k] != v) {
            *expected = v;
            *observed = regs[k];
            return k;
        }
    }
    return -1;
}
