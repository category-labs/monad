// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/debug.hpp>
#include <category/vm/interpreter/instruction_table.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/trampoline.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>

#if defined(MONAD_ZKVM_ZISK)
// The base of the handlers' slots, laid out by the linker script that
// zkvm/build-support writes: 256 per revision, the newest revision first, so
// that the revisions blocks run on sit nearest the functions their handlers
// call, the newest within a jal's reach.
extern "C" unsigned char const monad_vm_slots[];
#endif

namespace monad::vm::interpreter
{
#if defined(MONAD_ZKVM_ZISK)
    // One slot per revision and opcode: the opcode's handler, compiled into
    // it seven times. The section's name tells the linker script where to put
    // it (the revision in two decimal digits, the opcode in two hexadecimal
    // ones); an alignment attribute would not do it, since the assembler pads
    // to it with nops the linker relaxes away only after placing the
    // sections. The handler is reached by a tail call: through a plain one,
    // gcc inlines it but turns its own tail calls to Context::exit into
    // calls, and every handler gets a frame.
    // Each copy R (instruction_table.hpp's lag_offset) opens with 104 bytes
    // of heads, where SWAP1, PUSH2 and PUSH1 land on the opcode after them
    // (swap<1>, push<2>, push<1>), and the linker script places the copy
    // right after them. SWAP1's comes first (MONAD_VM_SWAP1_SWAP). In copy R,
    // PUSH1's head takes a PUSH1 (R + 5) % 7 bytes behind:
    // the immediate pushed, PUSH1's gas charged, and a5 stepped by 7 when the
    // copy is 0 or 1, in a3, a4 and a5, the handlers' stack_top,
    // gas_remaining and instr_ptr; it falls into the copy. Before it, PUSH2's
    // head takes a PUSH2 (R + 4) % 7 bytes behind: its stack test, its
    // immediate read, and a jump to the push in PUSH1's head. Where PUSH1
    // pairs with the opcode (push1_then), both heads are jumps, to the pair
    // and to PUSH2's push in full, placed past the slots; for JUMP and
    // JUMPI, PUSH2's head jumps to its pair (push2_then). The heads are
    // assembled without relaxation, so that nothing in them moves; a failed
    // stack test leaves through monad_vm_stack_overflow.
    #define MONAD_VM_LEAD_SECTION(                                             \
        NAME, OP, SUFFIX, PAD, HEADS, HEAD2, HEAD1, SIZE1)                     \
        asm(".pushsection .monad_vm_lead" #SUFFIX "." #NAME "." #OP            \
            ",\"ax\",@progbits\n"                                              \
            ".option push\n"                                                   \
            ".option norelax\n"                                                \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX         \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX         \
            ", 40\n"                                                           \
            "monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX               \
            ":\n" HEADS PAD "1:\ttail monad_vm_stack_overflow\n"               \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead2" #SUFFIX              \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead2" #SUFFIX ", 24\n"     \
            "monad_vm_slot_" #NAME "_" #OP "_lead2" #SUFFIX ":\n" HEAD2        \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead" #SUFFIX               \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead" #SUFFIX ", " SIZE1    \
            "\n"                                                               \
            "monad_vm_slot_" #NAME "_" #OP "_lead" #SUFFIX ":\n" HEAD1         \
            ".option pop\n"                                                    \
            ".popsection");
    // The seven copies' heads, copy 0 first.
    #define MONAD_VM_LEADS(                                                    \
        NAME,                                                                  \
        OP,                                                                    \
        H2_0,                                                                  \
        H1_0,                                                                  \
        H2_1,                                                                  \
        H1_1,                                                                  \
        H2_2,                                                                  \
        H1_2,                                                                  \
        H2_3,                                                                  \
        H1_3,                                                                  \
        H2_4,                                                                  \
        H1_4,                                                                  \
        H2_5,                                                                  \
        H1_5,                                                                  \
        H2_6,                                                                  \
        H1_6)                                                                  \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            ,                                                                  \
            "",                                                                \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 0),                                  \
            H2_0,                                                              \
            H1_0,                                                              \
            "32")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _1,                                                                \
            "",                                                                \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 1),                                  \
            H2_1,                                                              \
            H1_1,                                                              \
            "32")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _2,                                                                \
            "\tnop\n",                                                         \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 2),                                  \
            H2_2,                                                              \
            H1_2,                                                              \
            "28")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _3,                                                                \
            "\tnop\n",                                                         \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 3),                                  \
            H2_3,                                                              \
            H1_3,                                                              \
            "28")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _4,                                                                \
            "\tnop\n",                                                         \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 4),                                  \
            H2_4,                                                              \
            H1_4,                                                              \
            "28")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _5,                                                                \
            "\tnop\n",                                                         \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 5),                                  \
            H2_5,                                                              \
            H1_5,                                                              \
            "28")                                                              \
        MONAD_VM_LEAD_SECTION(                                                 \
            NAME,                                                              \
            OP,                                                                \
            _6,                                                                \
            "\tnop\n",                                                         \
            MONAD_VM_SWAP1_HEAD(NAME, OP, 6),                                  \
            H2_6,                                                              \
            H1_6,                                                              \
            "28")

    // SWAP1's head, 40 bytes ahead of the others: in copy R it takes a SWAP1
    // (R + 6) % 7 bytes behind (swap1_offset). For most opcodes it is the
    // swap through ctx's scratch word, a5 stepped by 7 in copy 0, and a jump
    // to the copy; POP's makes SWAP1 POP whole, the top's word moved down
    // once, and dispatches to POP's follower; JUMP's jumps to its pair.
    #define MONAD_VM_SWAP1_SWAP                                                \
        "\taddi t1, a0, 360\n"                                                 \
        "\tcsrs 0x813, a3\n"                                                   \
        "\taddi zero, t1, 32\n"                                                \
        "\taddi t4, a3, -32\n"                                                 \
        "\tcsrs 0x813, t4\n"                                                   \
        "\taddi zero, a3, 32\n"                                                \
        "\tcsrs 0x813, t1\n"                                                   \
        "\taddi zero, t4, 32\n"
    #define MONAD_VM_SWAP1_PLAIN_0(NAME, OP)                                   \
        MONAD_VM_SWAP1_SWAP MONAD_VM_STEP7 "\tj monad_vm_slot_" #NAME "_" #OP  \
                                           "\n"
    #define MONAD_VM_SWAP1_PLAIN_R(NAME, OP, SUFFIX)                           \
        MONAD_VM_SWAP1_SWAP "\tj monad_vm_slot_" #NAME "_" #OP SUFFIX          \
                            "\n\tnop\n"
    #define MONAD_VM_SWAP1_PLAIN_1(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_1")
    #define MONAD_VM_SWAP1_PLAIN_2(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_2")
    #define MONAD_VM_SWAP1_PLAIN_3(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_3")
    #define MONAD_VM_SWAP1_PLAIN_4(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_4")
    #define MONAD_VM_SWAP1_PLAIN_5(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_5")
    #define MONAD_VM_SWAP1_PLAIN_6(NAME, OP)                                   \
        MONAD_VM_SWAP1_PLAIN_R(NAME, OP, "_6")
    #define MONAD_VM_SWAP1_PLAIN(NAME, OP, R)                                  \
        MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_PLAIN_, R)(NAME, OP)
    // SWAP1 POP: the top's word one slot down, POP's gas, and POP's dispatch
    // to the copy one byte further behind (NEXT, the follower's offset from
    // a5, and JUMP, the copy's offset from the base).
    #define MONAD_VM_SWAP1_POP_AT(STEP, NEXT, JUMP, PAD)                       \
        STEP "\taddi t4, a3, -32\n"                                            \
             "\tcsrs 0x813, a3\n"                                              \
             "\taddi zero, t4, 32\n"                                           \
             "\taddi a3, a3, -32\n"                                            \
             "\taddi a4, a4, -2\n"                                             \
             "\tlbu a7, " NEXT "(a5)\n"                                        \
             "\tslli a7, a7, 12\n"                                             \
             "\tadd t3, a6, a7\n" JUMP PAD
    #define MONAD_VM_SWAP1_POP_0                                               \
        MONAD_VM_SWAP1_POP_AT(MONAD_VM_STEP7, "1", "\tjr 576(t3)\n", "")
    #define MONAD_VM_SWAP1_POP_1                                               \
        MONAD_VM_SWAP1_POP_AT("", "2", "\tjr 1160(t3)\n", "\tnop\n")
    #define MONAD_VM_SWAP1_POP_2                                               \
        MONAD_VM_SWAP1_POP_AT("", "3", "\tjr 1744(t3)\n", "\tnop\n")
    #define MONAD_VM_SWAP1_POP_3                                               \
        MONAD_VM_SWAP1_POP_AT("", "4", "\tjr -1760(t3)\n", "\tnop\n")
    #define MONAD_VM_SWAP1_POP_4                                               \
        MONAD_VM_SWAP1_POP_AT("", "5", "\tjr -1176(t3)\n", "\tnop\n")
    #define MONAD_VM_SWAP1_POP_5                                               \
        MONAD_VM_SWAP1_POP_AT("", "6", "\tjr -592(t3)\n", "\tnop\n")
    #define MONAD_VM_SWAP1_POP_6                                               \
        MONAD_VM_SWAP1_POP_AT("", "7", "\taddi a5, a5, 7\n\tjr 0(t3)\n", "")
    #define MONAD_VM_SWAP1_POP(NAME, OP, R)                                    \
        MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_POP_, R)
    #define MONAD_VM_SWAP1_JUMP(NAME, OP, R)                                   \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_swap1\n" MONAD_VM_NOP5         \
        "\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_SWAP1_OF_50 ~, POP
    #define MONAD_VM_SWAP1_OF_56 ~, JUMP
    #define MONAD_VM_SWAP1_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_, KIND)
    #define MONAD_VM_SWAP1_HEAD(NAME, OP, R)                                   \
        MONAD_VM_SWAP1_PICK(                                                   \
            MONAD_VM_LEAD_KIND(MONAD_VM_SWAP1_OF_##OP, PLAIN, ~))(NAME, OP, R)
    // SWAP1 JUMP's pair, past the slots: the jump does not read a5.
    #define MONAD_VM_SWAP1_PAIR_PLAIN(REV, NAME, OP)
    #define MONAD_VM_SWAP1_PAIR_POP(REV, NAME, OP)
    #define MONAD_VM_SWAP1_PAIR_JUMP(REV, NAME, OP)                            \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _swap1, ".monad_vm_swap1." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return swap1_jump<EvmTraits<REV>>(       \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                itbl);                                                         \
        }
    #define MONAD_VM_SWAP1_PAIR_PICK(KIND)                                     \
        MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_PAIR_, KIND)
    #define MONAD_VM_SWAP1_PAIR(REV, NAME, OP)                                 \
        MONAD_VM_SWAP1_PAIR_PICK(MONAD_VM_LEAD_KIND(                           \
            MONAD_VM_SWAP1_OF_##OP, PLAIN, ~))(REV, NAME, OP)

    // PUSH2's stack test, leaving through EXIT, and its immediate in t3.
    #define MONAD_VM_PUSH2_READ_AT(EXIT, HIGH, LOW)                            \
        "\tbgeu a3, a1, " EXIT "\n"                                            \
        "\tlbu t3, " HIGH "(a5)\n"                                             \
        "\tlbu t4, " LOW "(a5)\n"                                              \
        "\tpackh t3, t4, t3\n"
    // The push of t3 and PUSH1's gas.
    #define MONAD_VM_PUSH_T3                                                   \
        "\tsd t3, 32(a3)\n"                                                    \
        "\tsd zero, 40(a3)\n"                                                  \
        "\tsd zero, 48(a3)\n"                                                  \
        "\tsd zero, 56(a3)\n"                                                  \
        "\taddi a3, a3, 32\n"                                                  \
        "\taddi a4, a4, -3\n"
    #define MONAD_VM_STEP7 "\taddi a5, a5, 7\n"
    #define MONAD_VM_HEAD1_PUSH(IMM, STEP)                                     \
        "\tlbu t3, " IMM "(a5)\n3:\n" MONAD_VM_PUSH_T3 STEP
    #define MONAD_VM_HEAD2_PUSH(HIGH, LOW, STEP, PAD)                          \
        MONAD_VM_PUSH2_READ_AT("1b", HIGH, LOW) STEP "\tj 3f\n" PAD
    #define MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_HEAD_TO(TARGET, PAD) "\ttail " TARGET "\n" PAD
    // Copy by copy: PUSH1 from lag 5, 6, 0, 1, 2, 3, 4; PUSH2 from lag 4, 5,
    // 6, 0, 1, 2, 3.
    #define MONAD_VM_PLAIN1_0 MONAD_VM_HEAD1_PUSH("6", MONAD_VM_STEP7)
    #define MONAD_VM_PLAIN1_1 MONAD_VM_HEAD1_PUSH("7", MONAD_VM_STEP7)
    #define MONAD_VM_PLAIN1_2 MONAD_VM_HEAD1_PUSH("1", "")
    #define MONAD_VM_PLAIN1_3 MONAD_VM_HEAD1_PUSH("2", "")
    #define MONAD_VM_PLAIN1_4 MONAD_VM_HEAD1_PUSH("3", "")
    #define MONAD_VM_PLAIN1_5 MONAD_VM_HEAD1_PUSH("4", "")
    #define MONAD_VM_PLAIN1_6 MONAD_VM_HEAD1_PUSH("5", "")
    #define MONAD_VM_PLAIN2_0 MONAD_VM_HEAD2_PUSH("5", "6", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_1 MONAD_VM_HEAD2_PUSH("6", "7", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_2 MONAD_VM_HEAD2_PUSH("7", "8", MONAD_VM_STEP7, "")
    #define MONAD_VM_PLAIN2_3 MONAD_VM_HEAD2_PUSH("1", "2", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_4 MONAD_VM_HEAD2_PUSH("2", "3", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_5 MONAD_VM_HEAD2_PUSH("3", "4", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_6 MONAD_VM_HEAD2_PUSH("4", "5", "", "\tnop\n")
    // A jump head to a pair, which the linker script places past the slots:
    // a tail of 8 bytes (one step on ZisK, which folds the auipc into the
    // jump), PUSH2's head 24 bytes, PUSH1's 32 in copies 0 and 1, 28 after.
    #define MONAD_VM_TO2(NAME, OP, SUFFIX)                                     \
        MONAD_VM_HEAD_TO(                                                      \
            "monad_vm_slot_" #NAME "_" #OP "_push2" SUFFIX,                    \
            "\tnop\n\tnop\n\tnop\n\tnop\n")
    #define MONAD_VM_TO1_LONG(NAME, OP, SUFFIX)                                \
        MONAD_VM_HEAD_TO(                                                      \
            "monad_vm_slot_" #NAME "_" #OP "_push1" SUFFIX,                    \
            MONAD_VM_NOP5 "\tnop\n")
    #define MONAD_VM_TO1_SHORT(NAME, OP, SUFFIX)                               \
        MONAD_VM_HEAD_TO(                                                      \
            "monad_vm_slot_" #NAME "_" #OP "_push1" SUFFIX, MONAD_VM_NOP5)

    #define MONAD_VM_HANDLER_DECL(NAME, SUFFIX, SECTION)                       \
        extern "C"                                                             \
            [[gnu::section(SECTION)]] void monad_vm_slot_##NAME##SUFFIX(       \
                runtime::Context &ctx,                                         \
                MONAD_VM_ANALYSIS_PARAM,                                       \
                uint256_t const *const stack_bottom,                           \
                uint256_t *const stack_top,                                    \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const itbl)

    // The revision's traits LAG bytes behind.
    #define MONAD_VM_LAGT(REV, LAG)                                            \
        std::conditional_t<                                                    \
            (LAG) == 0,                                                        \
            EvmTraits<REV>,                                                    \
            Lagged<EvmTraits<REV>, (LAG)>>

    // The pair copy SUFFIX's head jumps to: compiled with instr_ptr LAG bytes
    // before its PUSH.
    #define MONAD_VM_PAIR_IN(REV, NAME, OP, PUSH, SUFFIX, LAG, ...)            \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP,                                                       \
            _##PUSH##SUFFIX,                                                   \
            ".monad_vm_" #PUSH #SUFFIX "." #NAME "." #OP)                      \
        {                                                                      \
            __attribute__((musttail)) return PUSH##_then<                      \
                0x##OP,                                                        \
                std::conditional_t<                                            \
                    pair_keeps_frame(0x##OP),                                  \
                    quiet_traits<MONAD_VM_LAGT(REV, LAG)>,                     \
                    MONAD_VM_LAGT(REV, LAG)>                                   \
                    __VA_OPT__(, ) __VA_ARGS__>(                               \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + (LAG),                                             \
                itbl);                                                         \
        }
    // PUSH1's pairs, copy by copy: from lag 5, 6, 0, 1, 2, 3, 4.
    #define MONAD_VM_PAIRS1(REV, NAME, OP, ...)                                \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, , 5, __VA_ARGS__)               \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _1, 6, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _2, 0, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _3, 1, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _4, 2, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _5, 3, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _6, 4, __VA_ARGS__)
    // PUSH2's: from lag 4, 5, 6, 0, 1, 2, 3.
    #define MONAD_VM_PAIRS2(REV, NAME, OP)                                     \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, , 4)                            \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _1, 5)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _2, 6)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _3, 0)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _4, 1)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _5, 2)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _6, 3)
    // PUSH2 in full before a follower PUSH1 pairs with, for copy SUFFIX's
    // head: from a lag of LAG, the immediate at HIGH and LOW, a5 stepped by
    // STEP, and a jump to the copy.
    #define MONAD_VM_PUSH2_IN(NAME, OP, SUFFIX, HIGH, LOW, STEP)               \
        asm(".pushsection .monad_vm_push2" #SUFFIX "." #NAME "." #OP           \
            ",\"ax\",@progbits\n"                                              \
            ".option push\n"                                                   \
            ".option norelax\n"                                                \
            ".type monad_vm_slot_" #NAME "_" #OP "_push2" #SUFFIX              \
            ", @function\n"                                                    \
            "monad_vm_slot_" #NAME "_" #OP "_push2" #SUFFIX                    \
            ":\n" MONAD_VM_PUSH2_READ_AT("2f", HIGH, LOW)                      \
                MONAD_VM_PUSH_T3 STEP                                          \
            "\ttail monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n"                 \
            "2:\ttail monad_vm_stack_overflow\n"                               \
            ".size monad_vm_slot_" #NAME "_" #OP "_push2" #SUFFIX ", . - "     \
            "monad_vm_slot_" #NAME "_" #OP "_push2" #SUFFIX "\n"               \
            ".option pop\n"                                                    \
            ".popsection");

    #define MONAD_VM_LEAD_PUSH(REV, NAME, OP)                                  \
        static_assert(                                                         \
            compiler::opcode_table<EvmTraits<REV>>[PUSH1].min_gas == 3 &&      \
            compiler::opcode_table<EvmTraits<REV>>[PUSH2].min_gas == 3 &&      \
            sizeof(uint256_t) == 32 && slot_lead == 1864 &&                    \
            swap1_back == 104 &&                                               \
            offsetof(runtime::Context, swap_scratch) == 360 &&                 \
            lag_offset(1) == 576 && lag_offset(2) == 1160 &&                   \
            lag_offset(3) == 1744 && lag_offset(4) == -1760 &&                 \
            lag_offset(5) == -1176 && lag_offset(6) == -592 &&                 \
            head_back(0, 1) == 32 && head_back(0, 2) == 56 &&                  \
            head_back(2, 1) == 28 && head_back(2, 2) == 52);                   \
        MONAD_VM_LEADS(                                                        \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_PLAIN2_0,                                                 \
            MONAD_VM_PLAIN1_0,                                                 \
            MONAD_VM_PLAIN2_1,                                                 \
            MONAD_VM_PLAIN1_1,                                                 \
            MONAD_VM_PLAIN2_2,                                                 \
            MONAD_VM_PLAIN1_2,                                                 \
            MONAD_VM_PLAIN2_3,                                                 \
            MONAD_VM_PLAIN1_3,                                                 \
            MONAD_VM_PLAIN2_4,                                                 \
            MONAD_VM_PLAIN1_4,                                                 \
            MONAD_VM_PLAIN2_5,                                                 \
            MONAD_VM_PLAIN1_5,                                                 \
            MONAD_VM_PLAIN2_6,                                                 \
            MONAD_VM_PLAIN1_6)

    #define MONAD_VM_LEAD_PAIR(REV, NAME, OP)                                  \
        MONAD_VM_LEADS(                                                        \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_TO2(NAME, OP, ""),                                        \
            MONAD_VM_TO1_LONG(NAME, OP, ""),                                   \
            MONAD_VM_TO2(NAME, OP, "_1"),                                      \
            MONAD_VM_TO1_LONG(NAME, OP, "_1"),                                 \
            MONAD_VM_TO2(NAME, OP, "_2"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_2"),                                \
            MONAD_VM_TO2(NAME, OP, "_3"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_3"),                                \
            MONAD_VM_TO2(NAME, OP, "_4"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_4"),                                \
            MONAD_VM_TO2(NAME, OP, "_5"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_5"),                                \
            MONAD_VM_TO2(NAME, OP, "_6"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_6"))                                \
        MONAD_VM_PUSH2_IN(NAME, OP, , "5", "6", MONAD_VM_STEP7)                \
        MONAD_VM_PUSH2_IN(NAME, OP, _1, "6", "7", MONAD_VM_STEP7)              \
        MONAD_VM_PUSH2_IN(NAME, OP, _2, "7", "8", MONAD_VM_STEP7)              \
        MONAD_VM_PUSH2_IN(NAME, OP, _3, "1", "2", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _4, "2", "3", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _5, "3", "4", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _6, "4", "5", "")                          \
        extern "C" [[gnu::section(".monad_vm_slot." #NAME "." #OP)]] void      \
            monad_vm_slot_##NAME##_##OP(                                       \
                runtime::Context &,                                            \
                MONAD_VM_ANALYSIS_TYPE,                                        \
                uint256_t const *,                                             \
                uint256_t *,                                                   \
                int64_t,                                                       \
                uint8_t const *,                                               \
                void const *);                                                 \
        MONAD_VM_PAIRS1(REV, NAME, OP, monad_vm_slot_##NAME##_##OP)

    // PUSH1's and PUSH2's pairs both: push1_then's and push2_then's.
    #define MONAD_VM_LEAD_PAIRS(REV, NAME, OP)                                 \
        MONAD_VM_LEADS(                                                        \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_TO2(NAME, OP, ""),                                        \
            MONAD_VM_TO1_LONG(NAME, OP, ""),                                   \
            MONAD_VM_TO2(NAME, OP, "_1"),                                      \
            MONAD_VM_TO1_LONG(NAME, OP, "_1"),                                 \
            MONAD_VM_TO2(NAME, OP, "_2"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_2"),                                \
            MONAD_VM_TO2(NAME, OP, "_3"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_3"),                                \
            MONAD_VM_TO2(NAME, OP, "_4"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_4"),                                \
            MONAD_VM_TO2(NAME, OP, "_5"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_5"),                                \
            MONAD_VM_TO2(NAME, OP, "_6"),                                      \
            MONAD_VM_TO1_SHORT(NAME, OP, "_6"))                                \
        MONAD_VM_PAIRS1(REV, NAME, OP)                                         \
        MONAD_VM_PAIRS2(REV, NAME, OP)

    #define MONAD_VM_LEAD_TWIN(REV, NAME, OP)                                  \
        MONAD_VM_LEADS(                                                        \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_TO2(NAME, OP, ""),                                        \
            MONAD_VM_PLAIN1_0,                                                 \
            MONAD_VM_TO2(NAME, OP, "_1"),                                      \
            MONAD_VM_PLAIN1_1,                                                 \
            MONAD_VM_TO2(NAME, OP, "_2"),                                      \
            MONAD_VM_PLAIN1_2,                                                 \
            MONAD_VM_TO2(NAME, OP, "_3"),                                      \
            MONAD_VM_PLAIN1_3,                                                 \
            MONAD_VM_TO2(NAME, OP, "_4"),                                      \
            MONAD_VM_PLAIN1_4,                                                 \
            MONAD_VM_TO2(NAME, OP, "_5"),                                      \
            MONAD_VM_PLAIN1_5,                                                 \
            MONAD_VM_TO2(NAME, OP, "_6"),                                      \
            MONAD_VM_PLAIN1_6)                                                 \
        MONAD_VM_PAIRS2(REV, NAME, OP)

    // The followers push1_then takes: ADD, SIGNEXTEND, NOT, AND, SHL, SHR,
    // SAR, CALLDATALOAD, MLOAD, MSTORE, PUSH1 and SWAP1 to SWAP4; and those
    // push2_then takes, JUMP, JUMPI, MLOAD and MSTORE. The others'
    // MONAD_VM_LEAD_OF_xx is undefined, and MONAD_VM_LEAD_KIND takes the
    // default after it.
    #define MONAD_VM_LEAD_OF_01 ~, PAIR
    #define MONAD_VM_LEAD_OF_0b ~, PAIR
    #define MONAD_VM_LEAD_OF_16 ~, PAIR
    #define MONAD_VM_LEAD_OF_19 ~, PAIR
    #define MONAD_VM_LEAD_OF_1b ~, PAIR
    #define MONAD_VM_LEAD_OF_1c ~, PAIR
    #define MONAD_VM_LEAD_OF_1d ~, PAIR
    #define MONAD_VM_LEAD_OF_35 ~, PAIR
    #define MONAD_VM_LEAD_OF_51 ~, PAIRS
    #define MONAD_VM_LEAD_OF_52 ~, PAIRS
    #define MONAD_VM_LEAD_OF_56 ~, TWIN
    #define MONAD_VM_LEAD_OF_57 ~, TWIN
    #define MONAD_VM_LEAD_OF_60 ~, PAIR
    #define MONAD_VM_LEAD_OF_90 ~, PAIR
    #define MONAD_VM_LEAD_OF_91 ~, PAIR
    #define MONAD_VM_LEAD_OF_92 ~, PAIR
    #define MONAD_VM_LEAD_OF_93 ~, PAIR
    #define MONAD_VM_LEAD_SECOND(A, B, ...) B
    #define MONAD_VM_LEAD_KIND(...) MONAD_VM_LEAD_SECOND(__VA_ARGS__)
    #define MONAD_VM_LEAD_CAT(A, B) A##B
    #define MONAD_VM_LEAD_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_LEAD_, KIND)
    #define MONAD_VM_LEAD(REV, NAME, OP)                                       \
        MONAD_VM_LEAD_PICK(                                                    \
            MONAD_VM_LEAD_KIND(MONAD_VM_LEAD_OF_##OP, PUSH, ~))(REV, NAME, OP)

    // Where a head's stack test leaves, ctx in a0 as in every handler.
    extern "C" void monad_vm_stack_overflow(runtime::Context &ctx)
    {
        __attribute__((musttail)) return ctx.exit(Error);
    }

    // Copy LAG of a handler: instr_ptr LAG bytes ahead of a5.
    #define MONAD_VM_COPY(REV, NAME, OP, SUFFIX, SECTION, LAG)                 \
        extern "C" [[gnu::section(SECTION "." #NAME "." #OP)]] void            \
            monad_vm_slot_##NAME##_##OP##SUFFIX(                               \
                runtime::Context &ctx,                                         \
                MONAD_VM_ANALYSIS_PARAM,                                       \
                uint256_t const *const stack_bottom,                           \
                uint256_t *const stack_top,                                    \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const itbl)                                        \
        {                                                                      \
            constexpr InstrEval handler = instruction_table<                   \
                Lagged<EvmTraits<REV>, LAG, !keeps_frame(0x##OP)>>[0x##OP];    \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + LAG,                                               \
                itbl);                                                         \
        }

    // Copy 0 of a handler, under the name SUFFIX ends.
    #define MONAD_VM_HANDLER(REV, NAME, OP, SUFFIX, SECTION)                   \
        extern "C" [[gnu::section(SECTION "." #NAME "." #OP)]] void            \
            monad_vm_slot_##NAME##_##OP##SUFFIX(                               \
                runtime::Context &ctx,                                         \
                MONAD_VM_ANALYSIS_PARAM,                                       \
                uint256_t const *const stack_bottom,                           \
                uint256_t *const stack_top,                                    \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const itbl)                                        \
        {                                                                      \
            constexpr InstrEval handler =                                      \
                instruction_table<std::conditional_t<                          \
                    keeps_frame(0x##OP),                                       \
                    quiet_traits<EvmTraits<REV>>,                              \
                    EvmTraits<REV>>>[0x##OP];                                  \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                itbl);                                                         \
        }

    #define MONAD_VM_SLOT_FULL(REV, NAME, OP)                                  \
        MONAD_VM_HANDLER(REV, NAME, OP, , ".monad_vm_slot")                    \
        MONAD_VM_COPY(REV, NAME, OP, _1, ".monad_vm_slot1", 1)                 \
        MONAD_VM_COPY(REV, NAME, OP, _2, ".monad_vm_slot2", 2)                 \
        MONAD_VM_COPY(REV, NAME, OP, _3, ".monad_vm_slot3", 3)                 \
        MONAD_VM_COPY(REV, NAME, OP, _4, ".monad_vm_slot4", 4)                 \
        MONAD_VM_COPY(REV, NAME, OP, _5, ".monad_vm_slot5", 5)                 \
        MONAD_VM_COPY(REV, NAME, OP, _6, ".monad_vm_slot6", 6)

    // A copy that jumps to the handler past the slots, a5 stepped by STEP.
    #define MONAD_VM_RELAY_IN(NAME, OP, SUFFIX, SECTION, STEP)                 \
        asm(".pushsection " SECTION "." #NAME "." #OP ",\"ax\",@progbits\n"    \
            ".option push\n"                                                   \
            ".option norelax\n"                                                \
            ".globl monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n"                 \
            ".type monad_vm_slot_" #NAME "_" #OP #SUFFIX ", @function\n"       \
            "monad_vm_slot_" #NAME "_" #OP #SUFFIX ":\n" STEP                  \
            "\ttail monad_vm_slot_" #NAME "_" #OP "_body\n"                    \
            ".size monad_vm_slot_" #NAME "_" #OP #SUFFIX                       \
            ", . - monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n"                  \
            ".option pop\n"                                                    \
            ".popsection");
    // A handler that outgrows a copy's region, DIV's, MOD's and ADDMOD's:
    // compiled once, past the slots, and each copy a jump there with a5
    // stepped by its lag (a call gcc made would inline the handler). The
    // others' MONAD_VM_RELAY_OF_xx is undefined, and MONAD_VM_SLOT takes the
    // full slot for them.
    #define MONAD_VM_SLOT_RELAY(REV, NAME, OP)                                 \
        MONAD_VM_HANDLER(REV, NAME, OP, _body, ".monad_vm_body")               \
        MONAD_VM_RELAY_IN(NAME, OP, , ".monad_vm_slot", "")                    \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _1, ".monad_vm_slot1", "\taddi a5, a5, 1\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _2, ".monad_vm_slot2", "\taddi a5, a5, 2\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _3, ".monad_vm_slot3", "\taddi a5, a5, 3\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _4, ".monad_vm_slot4", "\taddi a5, a5, 4\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _5, ".monad_vm_slot5", "\taddi a5, a5, 5\n")             \
        MONAD_VM_RELAY_IN(NAME, OP, _6, ".monad_vm_slot6", "\taddi a5, a5, 6\n")
    #define MONAD_VM_RELAY_OF_04 ~, RELAY
    #define MONAD_VM_RELAY_OF_06 ~, RELAY
    #define MONAD_VM_RELAY_OF_08 ~, RELAY
    #define MONAD_VM_RELAY_OF_20 ~, RELAY
    #define MONAD_VM_RELAY_OF_55 ~, RELAY
    #define MONAD_VM_SLOT_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SLOT_, KIND)

    #define MONAD_VM_SLOT(REV, NAME, OP)                                       \
        MONAD_VM_LEAD(REV, NAME, OP)                                           \
        MONAD_VM_SWAP1_PAIR(REV, NAME, OP)                                     \
        MONAD_VM_SLOT_PICK(MONAD_VM_LEAD_KIND(                                 \
            MONAD_VM_RELAY_OF_##OP, FULL, ~))(REV, NAME, OP)

    #define MONAD_VM_SLOTS_16(REV, NAME, H)                                    \
        MONAD_VM_SLOT(REV, NAME, H##0)                                         \
        MONAD_VM_SLOT(REV, NAME, H##1)                                         \
        MONAD_VM_SLOT(REV, NAME, H##2)                                         \
        MONAD_VM_SLOT(REV, NAME, H##3)                                         \
        MONAD_VM_SLOT(REV, NAME, H##4)                                         \
        MONAD_VM_SLOT(REV, NAME, H##5)                                         \
        MONAD_VM_SLOT(REV, NAME, H##6)                                         \
        MONAD_VM_SLOT(REV, NAME, H##7)                                         \
        MONAD_VM_SLOT(REV, NAME, H##8)                                         \
        MONAD_VM_SLOT(REV, NAME, H##9)                                         \
        MONAD_VM_SLOT(REV, NAME, H##a)                                         \
        MONAD_VM_SLOT(REV, NAME, H##b)                                         \
        MONAD_VM_SLOT(REV, NAME, H##c)                                         \
        MONAD_VM_SLOT(REV, NAME, H##d)                                         \
        MONAD_VM_SLOT(REV, NAME, H##e)                                         \
        MONAD_VM_SLOT(REV, NAME, H##f)

    #define MONAD_VM_SLOTS(REV, NAME)                                          \
        MONAD_VM_SLOTS_16(REV, NAME, 0)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 1)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 2)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 3)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 4)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 5)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 6)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 7)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 8)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, 9)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, a)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, b)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, c)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, d)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, e)                                        \
        MONAD_VM_SLOTS_16(REV, NAME, f)

    MONAD_VM_SLOTS(MONAD_ETH_BERLIN, 08)
    MONAD_VM_SLOTS(MONAD_ETH_LONDON, 09)
    MONAD_VM_SLOTS(MONAD_ETH_PARIS, 10)
    MONAD_VM_SLOTS(MONAD_ETH_SHANGHAI, 11)
    MONAD_VM_SLOTS(MONAD_ETH_CANCUN, 12)
    MONAD_VM_SLOTS(MONAD_ETH_PRAGUE, 13)
    MONAD_VM_SLOTS(MONAD_ETH_OSAKA, 14)
    MONAD_VM_SLOTS(MONAD_ETH_AMSTERDAM, 15)

    #undef MONAD_VM_SLOTS
    #undef MONAD_VM_SLOTS_16
    #undef MONAD_VM_SLOT
    #undef MONAD_VM_SLOT_PICK
    #undef MONAD_VM_RELAY_OF_55
    #undef MONAD_VM_RELAY_OF_20
    #undef MONAD_VM_RELAY_OF_08
    #undef MONAD_VM_RELAY_OF_06
    #undef MONAD_VM_RELAY_OF_04
    #undef MONAD_VM_SLOT_RELAY
    #undef MONAD_VM_RELAY_IN
    #undef MONAD_VM_SLOT_FULL
    #undef MONAD_VM_HANDLER
    #undef MONAD_VM_COPY
    #undef MONAD_VM_LEAD
    #undef MONAD_VM_LEAD_PICK
    #undef MONAD_VM_LEAD_CAT
    #undef MONAD_VM_LEAD_KIND
    #undef MONAD_VM_LEAD_SECOND
    #undef MONAD_VM_LEAD_OF_93
    #undef MONAD_VM_LEAD_OF_92
    #undef MONAD_VM_LEAD_OF_91
    #undef MONAD_VM_LEAD_OF_90
    #undef MONAD_VM_LEAD_OF_60
    #undef MONAD_VM_LEAD_OF_57
    #undef MONAD_VM_LEAD_OF_56
    #undef MONAD_VM_LEAD_OF_52
    #undef MONAD_VM_LEAD_OF_51
    #undef MONAD_VM_LEAD_OF_35
    #undef MONAD_VM_LEAD_OF_1d
    #undef MONAD_VM_LEAD_OF_1c
    #undef MONAD_VM_LEAD_OF_1b
    #undef MONAD_VM_LEAD_OF_19
    #undef MONAD_VM_LEAD_OF_16
    #undef MONAD_VM_LEAD_OF_0b
    #undef MONAD_VM_LEAD_OF_01
    #undef MONAD_VM_LEAD_TWIN
    #undef MONAD_VM_LEAD_PAIRS
    #undef MONAD_VM_LEAD_PAIR
    #undef MONAD_VM_LEAD_PUSH
    #undef MONAD_VM_PUSH2_IN
    #undef MONAD_VM_PAIRS2
    #undef MONAD_VM_PAIRS1
    #undef MONAD_VM_PAIR_IN
    #undef MONAD_VM_LAGT
    #undef MONAD_VM_HANDLER_DECL
    #undef MONAD_VM_TO1_SHORT
    #undef MONAD_VM_TO1_LONG
    #undef MONAD_VM_TO2
    #undef MONAD_VM_PLAIN2_6
    #undef MONAD_VM_PLAIN2_5
    #undef MONAD_VM_PLAIN2_4
    #undef MONAD_VM_PLAIN2_3
    #undef MONAD_VM_PLAIN2_2
    #undef MONAD_VM_PLAIN2_1
    #undef MONAD_VM_PLAIN2_0
    #undef MONAD_VM_PLAIN1_6
    #undef MONAD_VM_PLAIN1_5
    #undef MONAD_VM_PLAIN1_4
    #undef MONAD_VM_PLAIN1_3
    #undef MONAD_VM_PLAIN1_2
    #undef MONAD_VM_PLAIN1_1
    #undef MONAD_VM_PLAIN1_0
    #undef MONAD_VM_HEAD_TO
    #undef MONAD_VM_NOP5
    #undef MONAD_VM_HEAD2_PUSH
    #undef MONAD_VM_HEAD1_PUSH
    #undef MONAD_VM_STEP7
    #undef MONAD_VM_PUSH_T3
    #undef MONAD_VM_PUSH2_READ_AT
    #undef MONAD_VM_SWAP1_PAIR
    #undef MONAD_VM_SWAP1_PAIR_PICK
    #undef MONAD_VM_SWAP1_PAIR_JUMP
    #undef MONAD_VM_SWAP1_PAIR_POP
    #undef MONAD_VM_SWAP1_PAIR_PLAIN
    #undef MONAD_VM_SWAP1_HEAD
    #undef MONAD_VM_SWAP1_PICK
    #undef MONAD_VM_SWAP1_OF_56
    #undef MONAD_VM_SWAP1_OF_50
    #undef MONAD_VM_SWAP1_JUMP
    #undef MONAD_VM_SWAP1_POP
    #undef MONAD_VM_SWAP1_POP_6
    #undef MONAD_VM_SWAP1_POP_5
    #undef MONAD_VM_SWAP1_POP_4
    #undef MONAD_VM_SWAP1_POP_3
    #undef MONAD_VM_SWAP1_POP_2
    #undef MONAD_VM_SWAP1_POP_1
    #undef MONAD_VM_SWAP1_POP_0
    #undef MONAD_VM_SWAP1_POP_AT
    #undef MONAD_VM_SWAP1_PLAIN
    #undef MONAD_VM_SWAP1_PLAIN_6
    #undef MONAD_VM_SWAP1_PLAIN_5
    #undef MONAD_VM_SWAP1_PLAIN_4
    #undef MONAD_VM_SWAP1_PLAIN_3
    #undef MONAD_VM_SWAP1_PLAIN_2
    #undef MONAD_VM_SWAP1_PLAIN_1
    #undef MONAD_VM_SWAP1_PLAIN_R
    #undef MONAD_VM_SWAP1_PLAIN_0
    #undef MONAD_VM_SWAP1_SWAP
    #undef MONAD_VM_LEADS
    #undef MONAD_VM_LEAD_SECTION
#endif

    namespace
    {
        template <Traits traits>
        void core_loop(
            void *, runtime::Context *ctx, Intercode const *analysis,
            uint256_t *stack_ptr, void *)
        {
            auto *const stack_top = stack_ptr - 1;
            auto const *const stack_bottom =
                stack_top + MONAD_VM_STACK_BOTTOM_BIAS;
            auto const *const instr_ptr = analysis->code();
            auto const gas_remaining = ctx->gas_remaining;

            if constexpr (debug_enabled) {
                trace(*analysis, gas_remaining, instr_ptr);
            }
            // Resolve the table once for the tail-call chain.
#if defined(MONAD_ZKVM_ZISK)
            void const *itbl;
            if constexpr (has_slots<traits>) {
                itbl = monad_vm_slots +
                       ((MONAD_ETH_AMSTERDAM - traits::evm_rev())
                        << 8 << slot_shift) +
                       slot_lead;
            }
            else {
                itbl = instruction_table<traits>.data();
            }
            InstrEval const first = dispatch_table<traits>(itbl)[*instr_ptr];
#else
            InstrEval const first = instruction_table<traits>[*instr_ptr];
#endif
            first(
                *ctx,
#if defined(MONAD_ZKVM_ZISK)
                ctx->stack_limit,
#else
                *analysis,
#endif
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    template <Traits traits>
    void execute(
        runtime::Context &ctx, Intercode const &analysis, uint8_t *stack_ptr)
    {
        // Cache the last valid stack slot: stack_bottom + 1024.
        ctx.stack_limit = reinterpret_cast<uint256_t *>(stack_ptr) + 1023;

#if defined(MONAD_ZKVM_ZISK)
        // The carry-ins are fixed; ADD and SUB set the pointers on every call.
        ctx.add256_params.cin = 0;
        ctx.sub256_params.cin = 1;
        // What the jumps read of the code: the handlers' second argument is
        // the stack limit.
        ctx.landing_base = analysis.code() + 1;
        ctx.code_bound = analysis.size();
        ctx.jumpdest_words = analysis.jumpdest_words();
#endif
        trampoline(
            ctx,
            analysis,
            reinterpret_cast<uint256_t *>(stack_ptr),
            core_loop<traits>);
    }

    EXPLICIT_TRAITS(execute);
}
