/* SPDX-License-Identifier: GPL-2.0-or-later */
/* User-space only FP/SIMD lane. A user thread's FP/SIMD registers are saved and
 * restored by the kernel on preemption, signals, migration and suspend; this lane
 * keeps the token live in all of them. Never built into the kernel module. */
#ifndef BITOXIN_SIMD_H
#define BITOXIN_SIMD_H
#include "bitoxin_lane.h"
#ifdef __KERNEL__
#error "bitoxin_simd.h is user-space only"
#endif

struct bx_v128 { bx_u8 b[16]; };

/* NEON stage table (also the portable reference). n: not, e: ext #imm,
 * 6/3/1: rev64/rev32/rev16, b: rbit. Stages 16..30 invert 15..1. */
static const char bx_neon_kind[BX_SIMD_MAX + 2] = "_ne6be3en1eb6en33ne6be1ne3eb6en";
static const bx_u8 bx_neon_ext[BX_SIMD_MAX + 1] = { 0, 0, 3, 0, 0, 8, 0, 5, 0, 0,
    7, 0, 0, 1, 0, 0, 0, 0, 15, 0, 0, 9, 0, 0, 11, 0, 8, 0, 0, 13, 0 };

static inline struct bx_v128 bx_neon_step(unsigned k, struct bx_v128 a)
{
    struct bx_v128 r;
    unsigned i, g;
    switch (bx_neon_kind[k]) {
    case 'n':
        for (i = 0; i < 16; ++i) r.b[i] = (bx_u8)~a.b[i];
        break;
    case 'e':
        for (i = 0; i < 16; ++i) r.b[i] = a.b[(i + bx_neon_ext[k]) & 15U];
        break;
    case 'b':
        for (i = 0; i < 16; ++i) {
            bx_u8 x = a.b[i], y = 0;
            for (g = 0; g < 8; ++g)
                if (x & (1U << g)) y |= (bx_u8)(0x80U >> g);
            r.b[i] = y;
        }
        break;
    default:
        g = bx_neon_kind[k] == '6' ? 8 : bx_neon_kind[k] == '3' ? 4 : 2;
        for (i = 0; i < 16; ++i) r.b[i] = a.b[(i / g) * g + (g - 1 - i % g)];
        break;
    }
    return r;
}

static inline bx_u64 bx_v128_half(const struct bx_v128 *v, unsigned half)
{
    bx_u64 r = 0;
    int i;
    for (i = 7; i >= 0; --i) r = (r << 8) | v->b[half * 8U + (unsigned)i];
    return r;
}

static inline struct bx_v128 bx_v128_dup(bx_u64 token)
{
    struct bx_v128 v;
    unsigned i;
    for (i = 0; i < 8; ++i) v.b[i] = v.b[i + 8] = (bx_u8)(token >> (8 * i));
    return v;
}

/* Test builds: BX_SIMD_FAULT=p flips register p+1 after it is produced (every
 * bit; the sign on RISC-V F). BX_SIMD_FAULT_HALF=1 flips only bit 0 of its high
 * 64 bits instead (RISC-V F has no high half: bit 0 instead of the sign). */
#ifndef BX_SIMD_FAULT_HALF
#define BX_SIMD_FAULT_HALF 0
#endif
#define BX_SIMD_F(p, r) ".if " BX_STR(BX_SIMD_FAULT) " == " #p "\n\t"

/* bx_simd_lane(token, check, snapshot, status): the check word is not read; it
 * is pinned in operand C so a kind-5 trap follows the lane trap convention. */
#if defined(__aarch64__) && !defined(BX_PORTABLE)
#define BX_SIMD_NAMES { "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10", \
    "v11", "v12", "v13", "v14", "v15", "v16", "v17", "v18", "v19", "v20", "v21", \
    "v22", "v23", "v24", "v25", "v26", "v27", "v28", "v29", "v30" }
#define BX_SIMD_SIGN_ONLY 0
#define BX_SIMD_REGNO_BASE 1
#if BX_SIMD_FAULT_HALF
#define BX_N_FLIP(r) "umov x16, " r ".d[1]\n\teor x16, x16, #1\n\tins " r ".d[1], x16\n\t"
#else
#define BX_N_FLIP(r) "not " r ".16b, " r ".16b\n\t"
#endif
#define BX_N(p, op, r) op "\n\t" BX_SIMD_F(p, r) BX_N_FLIP(r) ".endif\n\t"
/* Both halves of v30 are compared with the GPR token in x0, not with v0, so a
 * faulty dup or a v0 flipped before its use (stage 1) is caught as well. */
static inline bx_u64 bx_simd_lane(bx_u64 token, bx_u64 check, bx_u64 *snapshot,
                                  bx_u32 *status)
{
    register bx_u64 x0 __asm__("x0") = token;
    register bx_u64 *x1 __asm__("x1") = snapshot;
    register bx_u64 x2 __asm__("x2") = 0;
    register bx_u64 x3 __asm__("x3") = check;
    __asm__ volatile(
        "dup v0.2d, x0\n\t"
        BX_N(0, "not v1.16b, v0.16b", "v1")
        BX_N(1, "ext v2.16b, v1.16b, v1.16b, #3", "v2")
        BX_N(2, "rev64 v3.16b, v2.16b", "v3")
        BX_N(3, "rbit v4.16b, v3.16b", "v4")
        BX_N(4, "ext v5.16b, v4.16b, v4.16b, #8", "v5")
        BX_N(5, "rev32 v6.16b, v5.16b", "v6")
        BX_N(6, "ext v7.16b, v6.16b, v6.16b, #5", "v7")
        BX_N(7, "not v8.16b, v7.16b", "v8")
        BX_N(8, "rev16 v9.16b, v8.16b", "v9")
        BX_N(9, "ext v10.16b, v9.16b, v9.16b, #7", "v10")
        BX_N(10, "rbit v11.16b, v10.16b", "v11")
        BX_N(11, "rev64 v12.16b, v11.16b", "v12")
        BX_N(12, "ext v13.16b, v12.16b, v12.16b, #1", "v13")
        BX_N(13, "not v14.16b, v13.16b", "v14")
        BX_N(14, "rev32 v15.16b, v14.16b", "v15")
        BX_N(15, "rev32 v16.16b, v15.16b", "v16")
        BX_N(16, "not v17.16b, v16.16b", "v17")
        BX_N(17, "ext v18.16b, v17.16b, v17.16b, #15", "v18")
        BX_N(18, "rev64 v19.16b, v18.16b", "v19")
        BX_N(19, "rbit v20.16b, v19.16b", "v20")
        BX_N(20, "ext v21.16b, v20.16b, v20.16b, #9", "v21")
        BX_N(21, "rev16 v22.16b, v21.16b", "v22")
        BX_N(22, "not v23.16b, v22.16b", "v23")
        BX_N(23, "ext v24.16b, v23.16b, v23.16b, #11", "v24")
        BX_N(24, "rev32 v25.16b, v24.16b", "v25")
        BX_N(25, "ext v26.16b, v25.16b, v25.16b, #8", "v26")
        BX_N(26, "rbit v27.16b, v26.16b", "v27")
        BX_N(27, "rev64 v28.16b, v27.16b", "v28")
        BX_N(28, "ext v29.16b, v28.16b, v28.16b, #13", "v29")
        BX_N(29, "not v30.16b, v29.16b", "v30")
        "umov x16, v30.d[0]\n\t" "umov x17, v30.d[1]\n\t"
        "eor x16, x16, x0\n\t" "eor x17, x17, x0\n\t" "orr x16, x16, x17\n\t"
        "cbnz x16, 9f\n\t" "umov x0, v30.d[0]\n\t" "b 7f\n"
        "9:\n\t" "mov x2, #5\n\t" "cbz x1, 5f\n\t"
        "st1 {v1.2d, v2.2d, v3.2d, v4.2d}, [x1], #64\n\t"
        "st1 {v5.2d, v6.2d, v7.2d, v8.2d}, [x1], #64\n\t"
        "st1 {v9.2d, v10.2d, v11.2d, v12.2d}, [x1], #64\n\t"
        "st1 {v13.2d, v14.2d, v15.2d, v16.2d}, [x1], #64\n\t"
        "st1 {v17.2d, v18.2d, v19.2d, v20.2d}, [x1], #64\n\t"
        "st1 {v21.2d, v22.2d, v23.2d, v24.2d}, [x1], #64\n\t"
        "st1 {v25.2d, v26.2d, v27.2d, v28.2d}, [x1], #64\n\t"
        "st1 {v29.2d, v30.2d}, [x1], #32\n\t"
        "umov x0, v30.d[0]\n\t" "b 7f\n"
        "5:\n\t" BX_A64_TRAP
        "7:\n"
        : "+r"(x0), "+r"(x1), "+r"(x2)
        : "r"(x3)
        : "v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10", "v11",
          "v12", "v13", "v14", "v15", "v16", "v17", "v18", "v19", "v20", "v21", "v22",
          "v23", "v24", "v25", "v26", "v27", "v28", "v29", "v30", "x16", "x17",
          "cc", "memory");
    *status = (bx_u32)x2;
    return x0;
}
#elif defined(__riscv) && __riscv_xlen == 64 && defined(__riscv_flen) && \
    __riscv_flen >= 64 && !defined(BX_PORTABLE)
#define BX_SIMD_NAMES { "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", \
    "f11", "f12", "f13", "f14", "f15", "f16", "f17", "f18", "f19", "f20", "f21", \
    "f22", "f23", "f24", "f25", "f26", "f27", "f28", "f29", "f30" }
#define BX_SIMD_SIGN_ONLY 1
#define BX_SIMD_REGNO_BASE 1
#if BX_SIMD_FAULT_HALF
#define BX_F_FLIP(d) "fmv.x.d t0, " d "\n\txori t0, t0, 1\n\tfmv.d.x " d ", t0\n\t"
#else
#define BX_F_FLIP(d) "fsgnjn.d " d ", " d ", " d "\n\t"
#endif
/* fsgnjn (sign negation) is a non-arithmetic move: no NaN canonicalisation. */
#define BX_F(p, d, s) "fsgnjn.d " d ", " s ", " s "\n\t" BX_SIMD_F(p, d) \
    BX_F_FLIP(d) ".endif\n\t"
static inline bx_u64 bx_simd_lane(bx_u64 token, bx_u64 check, bx_u64 *snapshot,
                                  bx_u32 *status)
{
    register bx_u64 a0 __asm__("a0") = token;
    register bx_u64 *a1 __asm__("a1") = snapshot;
    register bx_u64 a2 __asm__("a2") = 0;
    register bx_u64 a3 __asm__("a3") = check;
    /* s6: the marker word after ebreak decodes as auipc s6, 0 (see BX_RV_TRAP). */
    __asm__ volatile(
        "fmv.d.x f0, a0\n\t"
        BX_F(0, "f1", "f0") BX_F(1, "f2", "f1") BX_F(2, "f3", "f2")
        BX_F(3, "f4", "f3") BX_F(4, "f5", "f4") BX_F(5, "f6", "f5")
        BX_F(6, "f7", "f6") BX_F(7, "f8", "f7") BX_F(8, "f9", "f8")
        BX_F(9, "f10", "f9") BX_F(10, "f11", "f10") BX_F(11, "f12", "f11")
        BX_F(12, "f13", "f12") BX_F(13, "f14", "f13") BX_F(14, "f15", "f14")
        BX_F(15, "f16", "f15") BX_F(16, "f17", "f16") BX_F(17, "f18", "f17")
        BX_F(18, "f19", "f18") BX_F(19, "f20", "f19") BX_F(20, "f21", "f20")
        BX_F(21, "f22", "f21") BX_F(22, "f23", "f22") BX_F(23, "f24", "f23")
        BX_F(24, "f25", "f24") BX_F(25, "f26", "f25") BX_F(26, "f27", "f26")
        BX_F(27, "f28", "f27") BX_F(28, "f29", "f28") BX_F(29, "f30", "f29")
        "fmv.x.d t0, f30\n\t"
        "bne t0, a0, 9f\n\t" "mv a0, t0\n\t" "j 7f\n"
        "9:\n\t" "li a2, 5\n\t" "beqz a1, 5f\n\t"
        "fsd f1, 0(a1)\n\t" "fsd f2, 16(a1)\n\t" "fsd f3, 32(a1)\n\t"
        "fsd f4, 48(a1)\n\t" "fsd f5, 64(a1)\n\t" "fsd f6, 80(a1)\n\t"
        "fsd f7, 96(a1)\n\t" "fsd f8, 112(a1)\n\t" "fsd f9, 128(a1)\n\t"
        "fsd f10, 144(a1)\n\t" "fsd f11, 160(a1)\n\t" "fsd f12, 176(a1)\n\t"
        "fsd f13, 192(a1)\n\t" "fsd f14, 208(a1)\n\t" "fsd f15, 224(a1)\n\t"
        "fsd f16, 240(a1)\n\t" "fsd f17, 256(a1)\n\t" "fsd f18, 272(a1)\n\t"
        "fsd f19, 288(a1)\n\t" "fsd f20, 304(a1)\n\t" "fsd f21, 320(a1)\n\t"
        "fsd f22, 336(a1)\n\t" "fsd f23, 352(a1)\n\t" "fsd f24, 368(a1)\n\t"
        "fsd f25, 384(a1)\n\t" "fsd f26, 400(a1)\n\t" "fsd f27, 416(a1)\n\t"
        "fsd f28, 432(a1)\n\t" "fsd f29, 448(a1)\n\t" "fsd f30, 464(a1)\n\t"
        "mv a0, t0\n\t" "j 7f\n"
        "5:\n\t" BX_RV_TRAP
        "7:\n"
        : "+r"(a0), "+r"(a1), "+r"(a2)
        : "r"(a3)
        : "t0", "s6", "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "fs0",
          "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5", "fa6", "fa7", "fs2", "fs3",
          "fs4", "fs5", "fs6", "fs7", "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10",
          "memory");
    *status = (bx_u32)a2;
    return a0;
}
#else
#define BX_SIMD_NAMES { "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", \
    "s11", "s12", "s13", "s14", "s15", "s16", "s17", "s18", "s19", "s20", "s21", \
    "s22", "s23", "s24", "s25", "s26", "s27", "s28", "s29", "s30" }
#define BX_SIMD_SIGN_ONLY 0
#define BX_SIMD_REGNO_BASE -1
static inline bx_u64 bx_simd_lane(bx_u64 token, bx_u64 check, bx_u64 *snapshot,
                                  bx_u32 *status)
{
    struct bx_v128 v = bx_v128_dup(token), regs[BX_SIMD_MAX];
    unsigned p;
    for (p = 0; p < BX_SIMD_MAX; ++p) {
        v = bx_neon_step(p + 1, v);
        if ((int)p == BX_SIMD_FAULT) {
#if BX_SIMD_FAULT_HALF
            v.b[8] ^= 1U; /* bit 0 of the high half */
#else
            unsigned i;
            for (i = 0; i < 16; ++i) v.b[i] = (bx_u8)~v.b[i];
#endif
        }
        regs[p] = v;
    }
    if (bx_v128_half(&v, 0) == token && bx_v128_half(&v, 1) == token) {
        *status = BX_LANE_OK;
        return bx_v128_half(&v, 0);
    }
    *status = BX_LANE_SIMD;
    if (!snapshot)
        bx_trap_now(BX_LANE_SIMD, token, 0, check);
    for (p = 0; p < BX_SIMD_MAX; ++p) {
        snapshot[2 * p] = bx_v128_half(&regs[p], 0);
        snapshot[2 * p + 1] = bx_v128_half(&regs[p], 1);
    }
    return bx_v128_half(&v, 0);
}
#endif
#endif
