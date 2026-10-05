/* SPDX-License-Identifier: GPL-2.0-or-later */
#ifndef BITOXIN_CORE_H
#define BITOXIN_CORE_H
#ifdef __KERNEL__
#include <linux/types.h>
typedef u8 bx_u8;
typedef u32 bx_u32;
typedef u64 bx_u64;
#else
#include <stddef.h>
#include <stdint.h>
typedef uint8_t bx_u8;
typedef uint32_t bx_u32;
typedef uint64_t bx_u64;
#endif

#define BX_MIN_BYTES 64U
#define BX_MAX_BYTES (128U * 1024U * 1024U)
enum bx_phase { BX_WALK, BX_VERIFY };
enum bx_result { BX_OK, BX_BAD_CONFIG, BX_DATA_ERROR, BX_REGISTER_ERROR, BX_STATE_ERROR };
struct bx_error {
    enum bx_result code;
    enum bx_phase phase;
    bx_u32 bit;
    bx_u64 expected, observed, pass;
};
struct bx_probe {
    volatile bx_u8 *buffer;
    bx_u32 bytes, bits, seed, lfsr, taps, walked, verified;
    bx_u8 expected;
    enum bx_phase phase;
    bx_u64 passes, operations;
    struct bx_error error;
};
int bx_init(struct bx_probe *p, volatile bx_u8 *buffer, bx_u32 bytes, bx_u32 seed);
int bx_run(struct bx_probe *p, bx_u32 budget);
const char *bx_result_name(enum bx_result code);
const char *bx_backend_name(void);
#endif
