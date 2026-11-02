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
#define BX_LANE_MAX 24
#define BX_SIMD_MAX 30
#define BX_MAX_ROUNDS 65536U
#define BX_TRAP_MARKER 0x00000b17U
#define BX_AUDIT_UNLOCATED 0xffffffffU
enum bx_phase { BX_WALK, BX_VERIFY };
enum bx_result { BX_OK, BX_BAD_CONFIG, BX_DATA_ERROR, BX_REGISTER_ERROR, BX_STATE_ERROR };
enum bx_lane_status { BX_LANE_OK, BX_LANE_REGISTER, BX_LANE_MEMORY,
                      BX_LANE_DATA, BX_LANE_STATE, BX_LANE_SIMD };
enum bx_trap_reg { BX_TRAP_REG_A, BX_TRAP_REG_B, BX_TRAP_REG_KIND, BX_TRAP_REG_C };
struct bx_error {
    enum bx_result code;
    enum bx_phase phase;
    bx_u32 bit;
    bx_u64 expected, observed, pass;
    int lane_index;          /* first deviating chain position, -1 if none */
    bx_u8 lane_simd;         /* lane_index refers to the FP/SIMD chain */
    bx_u64 lane_expected, lane_observed;
};
struct bx_probe {
    volatile bx_u8 *buffer;
    bx_u32 bytes, bits, seed, lfsr, taps, walked, verified, cursor, rounds;
    bx_u8 expected, trap;
    enum bx_phase phase;
    bx_u64 passes, operations, audits;
    struct bx_error error;
    bx_u64 lane_regs[BX_LANE_MAX];
#ifdef BX_SIMD
    bx_u64 simd_regs[BX_SIMD_MAX * 2];
#endif
};
int bx_init(struct bx_probe *p, volatile bx_u8 *buffer, bx_u32 bytes, bx_u32 seed);
int bx_set_lane(struct bx_probe *p, bx_u32 rounds, int trap);
int bx_run(struct bx_probe *p, bx_u32 budget);
const char *bx_result_name(enum bx_result code);
const char *bx_backend_name(void);
int bx_lane_count(void);
const char *bx_lane_reg_name(int index);
int bx_lane_regno(int index);              /* architectural number, -1 if none */
int bx_trap_regno(enum bx_trap_reg reg);   /* architectural number, -1 if none */
int bx_lane_decode(bx_u64 token, const bx_u64 *regs, bx_u64 *expected, bx_u64 *observed);
#endif
