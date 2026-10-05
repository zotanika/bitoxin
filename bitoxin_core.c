/* SPDX-License-Identifier: GPL-2.0-or-later */
#include "bitoxin_core.h"
#include "bitoxin_lane.h"
#ifdef __KERNEL__
#include <linux/string.h>
#else
#include <string.h>
#endif

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

static int fail(struct bx_probe *p, enum bx_result code, bx_u32 bit,
                bx_u64 expected, bx_u64 observed)
{
    p->error.code = code;
    p->error.phase = p->phase;
    p->error.bit = bit;
    p->error.expected = expected;
    p->error.observed = observed;
    p->error.pass = p->passes;
    return code;
}

int bx_init(struct bx_probe *p, volatile bx_u8 *buffer, bx_u32 bytes, bx_u32 seed)
{
    bx_u32 i;
    if (!p) return BX_BAD_CONFIG;
    memset(p, 0, sizeof(*p));
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
    for (i = 0; i < bytes; ++i) buffer[i] = 0xff;
    return BX_OK;
}

int bx_run(struct bx_probe *p, bx_u32 budget)
{
    if (!p) return BX_BAD_CONFIG;
    if (p->error.code != BX_OK) return p->error.code;
    if (!p->buffer || !valid_size(p->bytes) || p->bits != p->bytes * 8U ||
        p->taps != mask_for(p->bytes) || !p->seed || p->seed >= p->bits ||
        !p->lfsr || p->lfsr >= p->bits || p->expected > 1 ||
        (p->phase != BX_WALK && p->phase != BX_VERIFY) ||
        p->walked > p->bits || p->verified > p->bytes ||
        (p->phase == BX_WALK && p->verified != 0))
        return fail(p, BX_STATE_ERROR, 0, 0, p->lfsr);

    while (budget--) {
        if (p->phase == BX_WALK) {
            bx_u32 index;
            bx_u8 observed, bit, mask;
            bx_u64 token, carried;
            if (p->walked >= p->bits)
                return fail(p, BX_STATE_ERROR, 0, p->bits - 1, p->walked);
            if (p->walked == p->bits - 1) {
                if (p->lfsr != p->seed)
                    return fail(p, BX_STATE_ERROR, 0, p->seed, p->lfsr);
                index = 0; /* Zero is outside the LFSR cycle, inside the test. */
            } else {
                p->lfsr = (p->lfsr >> 1) ^ ((0U - (p->lfsr & 1U)) & p->taps);
                index = p->lfsr;
            }
            observed = p->buffer[index >> 3];
            mask = (bx_u8)(1U << (index & 7U));
            bit = (observed & mask) != 0;
            if (bit != p->expected)
                return fail(p, BX_DATA_ERROR, index, p->expected, bit);

            /* Actual load in the low byte; varied upper bits exercise the GPRs.
             * The checked result supplies the store. No cache flush is implied. */
            token = (((bx_u64)index * 0x9e3779b97f4a7c15ULL) & ~0xffULL) | observed;
            carried = bx_register_lane(token);
            if (carried != token)
                return fail(p, BX_REGISTER_ERROR, index, token, carried);
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
#if defined(__aarch64__) && !defined(BX_PORTABLE)
    return "aarch64-gpr";
#else
    return "portable-c";
#endif
}
