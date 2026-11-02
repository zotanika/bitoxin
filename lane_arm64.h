/* SPDX-License-Identifier: GPL-2.0-or-later */
/* AArch64 lane: the token passes through every GPR the kernel does not reserve
 * (not x18, FP, LR, SP). Operands use x0-x3, the chain x4-x17 and x19-x28.
 * IRQs and preemption are untouched; every scratch register is declared. */
#define BX_LANE_REGS 24
#define BX_BACKEND_NAME "aarch64-gpr"
#define BX_LANE_NAMES { "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", \
    "x13", "x14", "x15", "x16", "x17", "x19", "x20", "x21", "x22", "x23", "x24", \
    "x25", "x26", "x27", "x28" }
#define BX_LANE_REGNOS { 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, \
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28 }
#define BX_TRAP_REGNOS { 0, 1, 2, 3 }
#define BX_A64_F(k, r) ".if " BX_STR(BX_LANE_FAULT) " == " #k "\n\t" \
    "eor " r ", " r ", #1\n\t.endif\n\t"
#define BX_A64_TRAP "brk #0xb17\n\t.inst 0x00000b17\n"

static inline bx_u64 bx_lane_ref_step(unsigned k, bx_u64 v)
{
    return bx_a64_step(k, v);
}

static inline void bx_trap_now(bx_u64 kind, bx_u64 a, bx_u64 b, bx_u64 c)
{
    register bx_u64 x0 __asm__("x0") = a;
    register bx_u64 x1 __asm__("x1") = b;
    register bx_u64 x2 __asm__("x2") = kind;
    register bx_u64 x3 __asm__("x3") = c;
    __asm__ volatile(BX_A64_TRAP : : "r"(x0), "r"(x1), "r"(x2), "r"(x3) : "memory");
}

static inline bx_u64 bx_lane(bx_u64 token, bx_u64 check, bx_u32 rounds,
                             bx_u64 *snapshot, bx_u32 *status)
{
    register bx_u64 x0 __asm__("x0") = token;
    register bx_u64 *x1 __asm__("x1") = snapshot;
    register bx_u64 x2 __asm__("x2") = rounds;
    register bx_u64 x3 __asm__("x3") = check;
    /* The bit check compares all of check >> 8 (not one bit), so a corrupted
     * expected value above 1 is a memory mismatch: stricter than portable. */
    __asm__ volatile(
        "and x4, x3, #7\n\t" "lsr x5, x0, x4\n\t" "and x5, x5, #1\n\t"
        "lsr x6, x3, #8\n\t" "eor x5, x5, x6\n\t" "cbnz x5, 8f\n\t"
        "mov x28, x0\n"
        "1:\n\t"
        "eor x4, x28, #0x5555555555555555\n\t" BX_A64_F(0, "x4")
        "ror x5, x4, #17\n\t" BX_A64_F(1, "x5")
        "add x6, x5, #0x7b1\n\t" BX_A64_F(2, "x6")
        "mvn x7, x6\n\t" BX_A64_F(3, "x7")
        "eor x8, x7, x7, lsr #32\n\t" BX_A64_F(4, "x8")
        "rbit x9, x8\n\t" BX_A64_F(5, "x9")
        "eor x10, x9, #0x0f0f0f0f0f0f0f0f\n\t" BX_A64_F(6, "x10")
        "ror x11, x10, #41\n\t" BX_A64_F(7, "x11")
        "sub x12, x11, #0x3c5\n\t" BX_A64_F(8, "x12")
        "rev x13, x12\n\t" BX_A64_F(9, "x13")
        "eor x14, x13, x13, lsl #32\n\t" BX_A64_F(10, "x14")
        "eor x15, x14, #0x00ff00ff00ff00ff\n\t" BX_A64_F(11, "x15")
        "eor x16, x15, #0x00ff00ff00ff00ff\n\t" BX_A64_F(12, "x16")
        "eor x17, x16, x16, lsl #32\n\t" BX_A64_F(13, "x17")
        "rev x19, x17\n\t" BX_A64_F(14, "x19")
        "add x20, x19, #0x3c5\n\t" BX_A64_F(15, "x20")
        "ror x21, x20, #23\n\t" BX_A64_F(16, "x21")
        "eor x22, x21, #0x0f0f0f0f0f0f0f0f\n\t" BX_A64_F(17, "x22")
        "rbit x23, x22\n\t" BX_A64_F(18, "x23")
        "eor x24, x23, x23, lsr #32\n\t" BX_A64_F(19, "x24")
        "mvn x25, x24\n\t" BX_A64_F(20, "x25")
        "sub x26, x25, #0x7b1\n\t" BX_A64_F(21, "x26")
        "ror x27, x26, #47\n\t" BX_A64_F(22, "x27")
        "eor x28, x27, #0x5555555555555555\n\t" BX_A64_F(23, "x28")
        "cmp x28, x0\n\t" "b.ne 9f\n\t"
        "subs x2, x2, #1\n\t" "b.ne 1b\n\t"
        "mov x0, x28\n\t" "b 7f\n"
        "8:\n\t" "mov x2, #2\n\t" "cbnz x1, 7f\n\t" "b 5f\n"
        "9:\n\t" "mov x2, #1\n\t" "cbz x1, 5f\n\t"
        "stp x4, x5, [x1, #0]\n\t" "stp x6, x7, [x1, #16]\n\t"
        "stp x8, x9, [x1, #32]\n\t" "stp x10, x11, [x1, #48]\n\t"
        "stp x12, x13, [x1, #64]\n\t" "stp x14, x15, [x1, #80]\n\t"
        "stp x16, x17, [x1, #96]\n\t" "stp x19, x20, [x1, #112]\n\t"
        "stp x21, x22, [x1, #128]\n\t" "stp x23, x24, [x1, #144]\n\t"
        "stp x25, x26, [x1, #160]\n\t" "stp x27, x28, [x1, #176]\n\t"
        "mov x0, x28\n\t" "b 7f\n"
        "5:\n\t" BX_A64_TRAP
        "7:\n"
        : "+r"(x0), "+r"(x1), "+r"(x2)
        : "r"(x3)
        : "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14",
          "x15", "x16", "x17", "x19", "x20", "x21", "x22", "x23", "x24", "x25",
          "x26", "x27", "x28", "cc", "memory");
    *status = (bx_u32)x2;
    return x0;
}
