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
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/interpreter/trampoline.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>

#if defined(MONAD_ZKVM_ZISK)
// Linker-defined base: 256 slots per revision, newest revision first to
// keep its handlers closer to runtime functions for short-range calls.
extern "C" unsigned char const monad_vm_slots[];
#endif

namespace monad::vm::interpreter
{
#if defined(MONAD_ZKVM_ZISK)
    // Each 4-KiB opcode slot holds six copies: actual instruction = a5 + lag.
    // Each copy has PUSH2/PUSH1 prefixes that execute the pending push, then
    // enter the follower, or tail-call a fused pair outside the slots.
    // Prefixes wrap the lag at the copy count, advancing a5 when needed.
    // a3 holds StackTop's next free slot, a1 the stack limit, and a4 the gas.
    // Disable relaxation to preserve offsets; musttail avoids native frames.
    #define MONAD_VM_LEAD_SECTION(NAME, OP, SUFFIX, PAD, HEAD2, HEAD1, SIZE1)  \
        asm(".pushsection .monad_vm_lead" #SUFFIX "." #NAME "." #OP            \
            ",\"ax\",@progbits\n"                                              \
            ".option push\n"                                                   \
            ".option norelax\n" PAD "1:\ttail monad_vm_stack_overflow\n"       \
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
    // The six copies' heads, copy 0 first.
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
        H1_5)                                                                  \
        MONAD_VM_LEAD_SECTION(NAME, OP, , "", H2_0, H1_0, "32")                \
        MONAD_VM_LEAD_SECTION(NAME, OP, _1, "", H2_1, H1_1, "32")              \
        MONAD_VM_LEAD_SECTION(NAME, OP, _2, "\tnop\n", H2_2, H1_2, "28")       \
        MONAD_VM_LEAD_SECTION(NAME, OP, _3, "\tnop\n", H2_3, H1_3, "28")       \
        MONAD_VM_LEAD_SECTION(NAME, OP, _4, "\tnop\n", H2_4, H1_4, "28")       \
        MONAD_VM_LEAD_SECTION(NAME, OP, _5, "\tnop\n", H2_5, H1_5, "28")

    // PUSH2's stack test, leaving through EXIT, and its immediate in t3.
    #define MONAD_VM_PUSH2_READ_AT(EXIT, HIGH, LOW)                            \
        "\tbgeu a3, a1, " EXIT "\n"                                            \
        "\tlbu t3, " HIGH "(a5)\n"                                             \
        "\tlbu t4, " LOW "(a5)\n"                                              \
        "\tpackh t3, t4, t3\n"
    // The push of t3 and PUSH1's gas.
    #define MONAD_VM_PUSH_T3                                                   \
        "\tsd t3, 0(a3)\n"                                                     \
        "\tsd zero, 8(a3)\n"                                                   \
        "\tsd zero, 16(a3)\n"                                                  \
        "\tsd zero, 24(a3)\n"                                                  \
        "\taddi a3, a3, 32\n"                                                  \
        "\taddi a4, a4, -3\n"
    #define MONAD_VM_STEP6 "\taddi a5, a5, 6\n"
    #define MONAD_VM_HEAD1_PUSH(IMM, STEP)                                     \
        "\tlbu t3, " IMM "(a5)\n3:\n" MONAD_VM_PUSH_T3 STEP
    #define MONAD_VM_HEAD2_PUSH(HIGH, LOW, STEP, PAD)                          \
        MONAD_VM_PUSH2_READ_AT("1b", HIGH, LOW) STEP "\tj 3f\n" PAD
    #define MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_HEAD_TO(TARGET, PAD) "\ttail " TARGET "\n" PAD
    // Copy by copy: PUSH1 from lag 4, 5, 0, 1, 2, 3; PUSH2 from lag 3, 4, 5,
    // 0, 1, 2.
    #define MONAD_VM_PLAIN1_0 MONAD_VM_HEAD1_PUSH("5", MONAD_VM_STEP6)
    #define MONAD_VM_PLAIN1_1 MONAD_VM_HEAD1_PUSH("6", MONAD_VM_STEP6)
    #define MONAD_VM_PLAIN1_2 MONAD_VM_HEAD1_PUSH("1", "")
    #define MONAD_VM_PLAIN1_3 MONAD_VM_HEAD1_PUSH("2", "")
    #define MONAD_VM_PLAIN1_4 MONAD_VM_HEAD1_PUSH("3", "")
    #define MONAD_VM_PLAIN1_5 MONAD_VM_HEAD1_PUSH("4", "")
    #define MONAD_VM_PLAIN2_0 MONAD_VM_HEAD2_PUSH("4", "5", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_1 MONAD_VM_HEAD2_PUSH("5", "6", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_2 MONAD_VM_HEAD2_PUSH("6", "7", MONAD_VM_STEP6, "")
    #define MONAD_VM_PLAIN2_3 MONAD_VM_HEAD2_PUSH("1", "2", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_4 MONAD_VM_HEAD2_PUSH("2", "3", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_5 MONAD_VM_HEAD2_PUSH("3", "4", "", "\tnop\n")
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
                MONAD_VM_DISPATCH_STATE_PARAM,                                 \
                uint256_t const *const stack_lower_bound,                      \
                StackTop const stack_top,                                      \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const table_base)

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
                Lagged<EvmTraits<REV>, LAG, !pair_keeps_frame(0x##OP)>         \
                    __VA_OPT__(, ) __VA_ARGS__>(                               \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + (LAG),                                             \
                table_base);                                                   \
        }
    // PUSH1's pairs, copy by copy: from lag 4, 5, 0, 1, 2, 3.
    #define MONAD_VM_PAIRS1(REV, NAME, OP, ...)                                \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, , 4, __VA_ARGS__)               \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _1, 5, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _2, 0, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _3, 1, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _4, 2, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _5, 3, __VA_ARGS__)
    // PUSH2's: from lag 3, 4, 5, 0, 1, 2.
    #define MONAD_VM_PAIRS2(REV, NAME, OP)                                     \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, , 3)                            \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _1, 4)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _2, 5)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _3, 0)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _4, 1)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _5, 2)
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
            sizeof(uint256_t) == 32 && slot_handler_offset == 1432 &&          \
            prefix_back_offset(0, 1) == 32 &&                                  \
            prefix_back_offset(0, 2) == 56 &&                                  \
            prefix_back_offset(2, 1) == 28 && prefix_back_offset(2, 2) == 52); \
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
            MONAD_VM_PLAIN1_5)

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
            MONAD_VM_TO1_SHORT(NAME, OP, "_5"))                                \
        MONAD_VM_PUSH2_IN(NAME, OP, , "4", "5", MONAD_VM_STEP6)                \
        MONAD_VM_PUSH2_IN(NAME, OP, _1, "5", "6", MONAD_VM_STEP6)              \
        MONAD_VM_PUSH2_IN(NAME, OP, _2, "6", "7", MONAD_VM_STEP6)              \
        MONAD_VM_PUSH2_IN(NAME, OP, _3, "1", "2", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _4, "2", "3", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _5, "3", "4", "")                          \
        extern "C" [[gnu::section(".monad_vm_slot." #NAME "." #OP)]] void      \
            monad_vm_slot_##NAME##_##OP(                                       \
                runtime::Context &,                                            \
                MONAD_VM_DISPATCH_STATE_TYPE,                                  \
                uint256_t const *,                                             \
                StackTop,                                                      \
                int64_t,                                                       \
                uint8_t const *,                                               \
                void const *);                                                 \
        MONAD_VM_PAIRS1(REV, NAME, OP, monad_vm_slot_##NAME##_##OP)

    // Both prefixes select a fusion: PUSH1 and PUSH2 with MLOAD/MSTORE.
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
            MONAD_VM_TO1_SHORT(NAME, OP, "_5"))                                \
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
            MONAD_VM_PLAIN1_5)                                                 \
        MONAD_VM_PAIRS2(REV, NAME, OP)

    // PAIR selects PUSH1 only, TWIN PUSH2 only, and PAIRS both fusions.
    // All other opcodes use ordinary prefixes. Suffixes are opcode hex values.
    #define MONAD_VM_LEAD_OF_01 ~, PAIR // ADD
    #define MONAD_VM_LEAD_OF_0b ~, PAIR // SIGNEXTEND
    #define MONAD_VM_LEAD_OF_16 ~, PAIR // AND
    #define MONAD_VM_LEAD_OF_19 ~, PAIR // NOT
    #define MONAD_VM_LEAD_OF_1b ~, PAIR // SHL
    #define MONAD_VM_LEAD_OF_1c ~, PAIR // SHR
    #define MONAD_VM_LEAD_OF_1d ~, PAIR // SAR
    #define MONAD_VM_LEAD_OF_35 ~, PAIR // CALLDATALOAD
    #define MONAD_VM_LEAD_OF_51 ~, PAIRS // MLOAD
    #define MONAD_VM_LEAD_OF_52 ~, PAIRS // MSTORE
    #define MONAD_VM_LEAD_OF_56 ~, TWIN // JUMP
    #define MONAD_VM_LEAD_OF_57 ~, TWIN // JUMPI
    #define MONAD_VM_LEAD_OF_60 ~, PAIR // PUSH1
    #define MONAD_VM_LEAD_OF_90 ~, PAIR // SWAP1
    #define MONAD_VM_LEAD_OF_91 ~, PAIR // SWAP2
    #define MONAD_VM_LEAD_OF_92 ~, PAIR // SWAP3
    #define MONAD_VM_LEAD_OF_93 ~, PAIR // SWAP4
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
                MONAD_VM_DISPATCH_STATE_PARAM,                                 \
                uint256_t const *const stack_lower_bound,                      \
                StackTop const stack_top,                                      \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const table_base)                                  \
        {                                                                      \
            constexpr InstrEval handler = instruction_table<                   \
                Lagged<EvmTraits<REV>, LAG, !keeps_frame(0x##OP)>>[0x##OP];    \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + LAG,                                               \
                table_base);                                                   \
        }

    #define MONAD_VM_SLOT_FULL(REV, NAME, OP)                                  \
        MONAD_VM_COPY(REV, NAME, OP, , ".monad_vm_slot", 0)                    \
        MONAD_VM_COPY(REV, NAME, OP, _1, ".monad_vm_slot1", 1)                 \
        MONAD_VM_COPY(REV, NAME, OP, _2, ".monad_vm_slot2", 2)                 \
        MONAD_VM_COPY(REV, NAME, OP, _3, ".monad_vm_slot3", 3)                 \
        MONAD_VM_COPY(REV, NAME, OP, _4, ".monad_vm_slot4", 4)                 \
        MONAD_VM_COPY(REV, NAME, OP, _5, ".monad_vm_slot5", 5)

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
    // Oversized handlers have one body outside the slots. Each copy first
    // advances a5 by its lag, then jumps there. Use assembly so GCC cannot
    // inline the body back into the slot. Other opcodes use SLOT_FULL.
    #define MONAD_VM_SLOT_RELAY(REV, NAME, OP)                                 \
        MONAD_VM_COPY(REV, NAME, OP, _body, ".monad_vm_body", 0)               \
        MONAD_VM_RELAY_IN(NAME, OP, , ".monad_vm_slot", "")                    \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _1, ".monad_vm_slot1", "\taddi a5, a5, 1\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _2, ".monad_vm_slot2", "\taddi a5, a5, 2\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _3, ".monad_vm_slot3", "\taddi a5, a5, 3\n")             \
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _4, ".monad_vm_slot4", "\taddi a5, a5, 4\n")             \
        MONAD_VM_RELAY_IN(NAME, OP, _5, ".monad_vm_slot5", "\taddi a5, a5, 5\n")
    #define MONAD_VM_RELAY_OF_04 ~, RELAY // DIV
    #define MONAD_VM_RELAY_OF_06 ~, RELAY // MOD
    #define MONAD_VM_RELAY_OF_08 ~, RELAY // ADDMOD
    // These bodies exceed a copy region with the current runtime inlining.
    #define MONAD_VM_RELAY_OF_37 ~, RELAY // CALLDATACOPY
    #define MONAD_VM_RELAY_OF_39 ~, RELAY // CODECOPY
    #define MONAD_VM_RELAY_OF_3e ~, RELAY // RETURNDATACOPY
    #define MONAD_VM_RELAY_OF_55 ~, RELAY // SSTORE
    #define MONAD_VM_RELAY_OF_5e ~, RELAY // MCOPY
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        // DUP1's extra gas checks exceed a copy region in verification mode.
        #define MONAD_VM_RELAY_OF_80 ~, RELAY // DUP1
    #endif
    #define MONAD_VM_SLOT_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SLOT_, KIND)

    #define MONAD_VM_SLOT(REV, NAME, OP)                                       \
        MONAD_VM_LEAD(REV, NAME, OP)                                           \
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

    MONAD_VM_SLOTS(EvmRevision::Berlin, 08)
    MONAD_VM_SLOTS(EvmRevision::London, 09)
    MONAD_VM_SLOTS(EvmRevision::Paris, 10)
    MONAD_VM_SLOTS(EvmRevision::Shanghai, 11)
    MONAD_VM_SLOTS(EvmRevision::Cancun, 12)
    MONAD_VM_SLOTS(EvmRevision::Prague, 13)
    MONAD_VM_SLOTS(EvmRevision::Osaka, 14)
    MONAD_VM_SLOTS(EvmRevision::Amsterdam, 15)

    #undef MONAD_VM_SLOTS
    #undef MONAD_VM_SLOTS_16
    #undef MONAD_VM_SLOT
    #undef MONAD_VM_RELAY_OF_80
    #undef MONAD_VM_SLOT_PICK
    #undef MONAD_VM_RELAY_OF_37
    #undef MONAD_VM_RELAY_OF_39
    #undef MONAD_VM_RELAY_OF_3e
    #undef MONAD_VM_RELAY_OF_55
    #undef MONAD_VM_RELAY_OF_5e
    #undef MONAD_VM_RELAY_OF_08
    #undef MONAD_VM_RELAY_OF_06
    #undef MONAD_VM_RELAY_OF_04
    #undef MONAD_VM_SLOT_RELAY
    #undef MONAD_VM_RELAY_IN
    #undef MONAD_VM_SLOT_FULL
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
    #undef MONAD_VM_HANDLER_DECL
    #undef MONAD_VM_TO1_SHORT
    #undef MONAD_VM_TO1_LONG
    #undef MONAD_VM_TO2
    #undef MONAD_VM_PLAIN2_5
    #undef MONAD_VM_PLAIN2_4
    #undef MONAD_VM_PLAIN2_3
    #undef MONAD_VM_PLAIN2_2
    #undef MONAD_VM_PLAIN2_1
    #undef MONAD_VM_PLAIN2_0
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
    #undef MONAD_VM_STEP6
    #undef MONAD_VM_PUSH_T3
    #undef MONAD_VM_PUSH2_READ_AT
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
            StackTop const stack_top{stack_ptr};
            auto const *const stack_lower_bound =
                stack_ptr + MONAD_VM_STACK_LOWER_BOUND_BIAS;
#if defined(MONAD_ZKVM_ZISK)
            ctx->frame_stack_lower_bound = stack_lower_bound;
#endif
            auto const *const instr_ptr = analysis->code();
            auto const gas_remaining = ctx->gas_remaining;

            if constexpr (debug_enabled) {
                trace(*analysis, gas_remaining, instr_ptr);
            }
            // Resolve the table once for the tail-call chain.
#if defined(MONAD_ZKVM_ZISK)
            using entry_traits = Lagged<traits, 0>;
            void const *table_base;
            if constexpr (has_slots<entry_traits>) {
                table_base = monad_vm_slots +
                             ((static_cast<unsigned>(EvmRevision::Amsterdam) -
                               static_cast<unsigned>(traits::evm_rev()))
                              << 8 << slot_shift) +
                             slot_handler_offset;
            }
            else {
                table_base = instruction_table<entry_traits>.data();
            }
            InstrEval const first =
                dispatch_table<entry_traits>(table_base)[*instr_ptr];
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
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    template <Traits traits>
    void execute(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t *const stack_ptr)
    {
        // Cache the one-past stack limit for comparisons with
        // StackTop::next_slot().
        ctx.stack_limit = stack_ptr + runtime::EvmStackAllocatorMeta::size;

#if defined(MONAD_ZKVM_ZISK)
        // The carry-ins are fixed; ADD and SUB set the pointers on every call.
        ctx.add256_params.cin = 0;
        ctx.sub256_params.cin = 1;
        // Keep code metadata in ctx; handlers pass the stack limit instead.
        ctx.landing_base = analysis.code() + 1;
        ctx.code_bound = analysis.size();
        ctx.jumpdest_words = analysis.jumpdest_words();
#endif
        trampoline<core_loop<traits>>(ctx, analysis, stack_ptr);
    }

    EXPLICIT_TRAITS(execute);
}
