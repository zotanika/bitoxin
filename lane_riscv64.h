/* SPDX-License-Identifier: GPL-2.0-or-later */
/* RV64 lane (base integer ISA only, no Zbb): the token passes through every GPR
 * the kernel does not reserve (not ra, sp, gp, tp, s0/fp). Operands use a0-a3. */
#define BX_LANE_REGS 22
#define BX_BACKEND_NAME "riscv64-gpr"
#define BX_LANE_NAMES { "t0", "t1", "t2", "s1", "a4", "a5", "a6", "a7", "s2", "s3", \
    "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6" }
#define BX_LANE_REGNOS { 5, 6, 7, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, \
    25, 26, 27, 28, 29, 30, 31 }
#define BX_TRAP_REGNOS { 10, 11, 12, 13 }
#define BX_RV_F(k, r) ".if " BX_STR(BX_LANE_FAULT) " == " #k "\n\t" \
    "xori " r ", " r ", 1\n\t.endif\n\t"
/* d = s ^ (s >> 32) or d = s ^ (s << 32), using d as the temporary. */
#define BX_RV_SX(op, d, s) op " " d ", " s ", 32\n\txor " d ", " d ", " s "\n\t"
/* The trap is non-resumable: the marker word 0x00000b17 decodes as auipc s6, 0,
 * so execution past it would write s6. With compressed code elsewhere the marker
 * may be only 2-byte aligned: read it with memcpy / copy_from_kernel_nofault,
 * never a direct u32 load. */
#define BX_RV_TRAP ".option push\n\t.option norvc\n\tebreak\n\t.option pop\n\t" \
    ".4byte 0x00000b17\n"

static inline bx_u64 bx_lane_ref_step(unsigned k, bx_u64 v)
{
    switch (k) {
    case 0: case 21: return v ^ 0x555U;
    case 1: return v + 0x7b1U;
    case 2: case 19: return ~v;
    case 3: case 9: case 12: case 18: return v ^ (v >> 32);
    case 4: case 17: return v ^ 0xfffffffffffffd55ULL; /* xori -0x2ab */
    case 5: return v - 0x3c5U;
    case 6: case 15: return v ^ (v << 32);
    case 7: case 14: return v ^ 0x0f0U;
    case 8: return v + 0x123U;
    case 10: case 11: return v ^ 0xfffffffffffff900ULL; /* xori -0x700 */
    case 13: return v - 0x123U;
    case 16: return v + 0x3c5U;
    case 20: default: return v - 0x7b1U;
    }
}

static inline void bx_trap_now(bx_u64 kind, bx_u64 a, bx_u64 b, bx_u64 c)
{
    register bx_u64 a0 __asm__("a0") = a;
    register bx_u64 a1 __asm__("a1") = b;
    register bx_u64 a2 __asm__("a2") = kind;
    register bx_u64 a3 __asm__("a3") = c;
    __asm__ volatile(BX_RV_TRAP : : "r"(a0), "r"(a1), "r"(a2), "r"(a3) : "s6", "memory");
}

static inline bx_u64 bx_lane(bx_u64 token, bx_u64 check, bx_u32 rounds,
                             bx_u64 *snapshot, bx_u32 *status)
{
    register bx_u64 a0 __asm__("a0") = token;
    register bx_u64 *a1 __asm__("a1") = snapshot;
    register bx_u64 a2 __asm__("a2") = rounds;
    register bx_u64 a3 __asm__("a3") = check;
    /* The bit check compares all of check >> 8 (not one bit), so a corrupted
     * expected value above 1 is a memory mismatch: stricter than portable. */
    __asm__ volatile(
        "andi t0, a3, 7\n\t" "srl t1, a0, t0\n\t" "andi t1, t1, 1\n\t"
        "srli t2, a3, 8\n\t" "xor t1, t1, t2\n\t" "bnez t1, 8f\n\t"
        "mv t6, a0\n"
        "1:\n\t"
        "xori t0, t6, 0x555\n\t" BX_RV_F(0, "t0")
        "addi t1, t0, 0x7b1\n\t" BX_RV_F(1, "t1")
        "not t2, t1\n\t" BX_RV_F(2, "t2")
        BX_RV_SX("srli", "s1", "t2") BX_RV_F(3, "s1")
        "xori a4, s1, -0x2ab\n\t" BX_RV_F(4, "a4")
        "addi a5, a4, -0x3c5\n\t" BX_RV_F(5, "a5")
        BX_RV_SX("slli", "a6", "a5") BX_RV_F(6, "a6")
        "xori a7, a6, 0x0f0\n\t" BX_RV_F(7, "a7")
        "addi s2, a7, 0x123\n\t" BX_RV_F(8, "s2")
        BX_RV_SX("srli", "s3", "s2") BX_RV_F(9, "s3")
        "xori s4, s3, -0x700\n\t" BX_RV_F(10, "s4")
        "xori s5, s4, -0x700\n\t" BX_RV_F(11, "s5")
        BX_RV_SX("srli", "s6", "s5") BX_RV_F(12, "s6")
        "addi s7, s6, -0x123\n\t" BX_RV_F(13, "s7")
        "xori s8, s7, 0x0f0\n\t" BX_RV_F(14, "s8")
        BX_RV_SX("slli", "s9", "s8") BX_RV_F(15, "s9")
        "addi s10, s9, 0x3c5\n\t" BX_RV_F(16, "s10")
        "xori s11, s10, -0x2ab\n\t" BX_RV_F(17, "s11")
        BX_RV_SX("srli", "t3", "s11") BX_RV_F(18, "t3")
        "not t4, t3\n\t" BX_RV_F(19, "t4")
        "addi t5, t4, -0x7b1\n\t" BX_RV_F(20, "t5")
        "xori t6, t5, 0x555\n\t" BX_RV_F(21, "t6")
        "bne t6, a0, 9f\n\t"
        "addi a2, a2, -1\n\t" "bnez a2, 1b\n\t"
        "mv a0, t6\n\t" "j 7f\n"
        "8:\n\t" "li a2, 2\n\t" "bnez a1, 7f\n\t" "j 5f\n"
        "9:\n\t" "li a2, 1\n\t" "beqz a1, 5f\n\t"
        "sd t0, 0(a1)\n\t" "sd t1, 8(a1)\n\t" "sd t2, 16(a1)\n\t" "sd s1, 24(a1)\n\t"
        "sd a4, 32(a1)\n\t" "sd a5, 40(a1)\n\t" "sd a6, 48(a1)\n\t" "sd a7, 56(a1)\n\t"
        "sd s2, 64(a1)\n\t" "sd s3, 72(a1)\n\t" "sd s4, 80(a1)\n\t" "sd s5, 88(a1)\n\t"
        "sd s6, 96(a1)\n\t" "sd s7, 104(a1)\n\t" "sd s8, 112(a1)\n\t" "sd s9, 120(a1)\n\t"
        "sd s10, 128(a1)\n\t" "sd s11, 136(a1)\n\t" "sd t3, 144(a1)\n\t"
        "sd t4, 152(a1)\n\t" "sd t5, 160(a1)\n\t" "sd t6, 168(a1)\n\t"
        "mv a0, t6\n\t" "j 7f\n"
        "5:\n\t" BX_RV_TRAP
        "7:\n"
        : "+r"(a0), "+r"(a1), "+r"(a2)
        : "r"(a3)
        : "t0", "t1", "t2", "s1", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5",
          "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6", "memory");
    *status = (bx_u32)a2;
    return a0;
}
