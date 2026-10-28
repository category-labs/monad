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
    // File-scope assembly needs a literal offset. Check it against the C++
    // layout.
    #define MONAD_VM_DEFINE_SWAP_SCRATCH_OFFSET(BYTES)                         \
        static_assert(offsetof(runtime::Context, swap_scratch) == (BYTES));    \
        asm(".equ monad_vm_swap_scratch_offset, " #BYTES)
    #if defined(MONAD_ZKVM_WIDE_MEMORY_SIZE)
    MONAD_VM_DEFINE_SWAP_SCRATCH_OFFSET(352);
    #else
    MONAD_VM_DEFINE_SWAP_SCRATCH_OFFSET(328);
    #endif
    #undef MONAD_VM_DEFINE_SWAP_SCRATCH_OFFSET

    #if defined(MONAD_ZKVM_NO_SWAP1_PREFIX)
        #define MONAD_VM_SWAP1_SECTION(NAME, OP, COPY, SUFFIX) ""
    #else
        #define MONAD_VM_SWAP1_SECTION(NAME, OP, COPY, SUFFIX)                 \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX         \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX         \
            ", 40\n"                                                           \
            "monad_vm_slot_" #NAME "_" #OP "_lead_swap1" #SUFFIX               \
            ":\n" MONAD_VM_SWAP1_HEAD(NAME, OP, COPY, SUFFIX)
    #endif

    #if defined(MONAD_ZKVM_NO_DUP_FUSION)
        #define MONAD_VM_DUP_SECTION(NAME, OP, SUFFIX) ""
        #define MONAD_VM_SEVENTH_COPY(...) __VA_ARGS__
        #define MONAD_VM_GROUP_SIZE "7"
    #else
        #define MONAD_VM_DUP_SECTION(NAME, OP, SUFFIX)                         \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead_dup" #SUFFIX           \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead_dup" #SUFFIX ", 40\n"  \
            "monad_vm_slot_" #NAME "_" #OP "_lead_dup" #SUFFIX                 \
            ":\n" MONAD_VM_DUP_HEAD(NAME, OP, SUFFIX)
        #define MONAD_VM_SEVENTH_COPY(...)
        #define MONAD_VM_GROUP_SIZE "6"
    #endif
    #if defined(MONAD_ZKVM_NO_SWAPN_FUSION)
        #define MONAD_VM_SWAPN_SECTION(NAME, OP, COPY, SUFFIX) ""
    #else
        #define MONAD_VM_SWAPN_SECTION(NAME, OP, COPY, SUFFIX)                 \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead_swapn" #SUFFIX         \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead_swapn" #SUFFIX         \
            ", 40\n"                                                           \
            "monad_vm_slot_" #NAME "_" #OP "_lead_swapn" #SUFFIX               \
            ":\n" MONAD_VM_SWAPN_HEAD(NAME, OP, COPY, SUFFIX)
    #endif
    #if defined(MONAD_ZKVM_NO_COMPARISON_FUSION)
        #define MONAD_VM_BOOL_SECTION(NAME, OP, COPY, SUFFIX) ""
    #else
        #define MONAD_VM_BOOL_SECTION(NAME, OP, COPY, SUFFIX)                  \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead_bool" #SUFFIX          \
            ", @function\n"                                                    \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead_bool" #SUFFIX ", 28\n" \
            "monad_vm_slot_" #NAME "_" #OP "_lead_bool" #SUFFIX                \
            ":\n" MONAD_VM_BOOL_HEAD(NAME, OP, COPY, SUFFIX)
    // Match the actual optional prefixes emitted below. File-scope extended
    // assembly cannot use C++ constexpr operands under GCC LTO.
    asm(".equ monad_vm_compare_distance, 92");
        #if !defined(MONAD_ZKVM_NO_DUP_FUSION)
    asm(".set monad_vm_compare_distance, monad_vm_compare_distance + 40");
        #endif
        #if !defined(MONAD_ZKVM_NO_SWAP1_PREFIX)
    asm(".set monad_vm_compare_distance, monad_vm_compare_distance + 40");
        #endif
        #if !defined(MONAD_ZKVM_NO_SWAPN_FUSION)
    asm(".set monad_vm_compare_distance, monad_vm_compare_distance + 40");
        #endif
    #endif
    // Each 4-KiB opcode slot holds six copies with DUP prefixes or seven
    // without them. Each copy starts with: [optional comparison: 28][optional
    // SWAPn: 40][optional DUPn: 40][optional SWAP1: 40][overflow, PUSH2, PUSH1:
    // 64 bytes][handler]. Prefixes execute the pending stack operation or jump
    // to a fused pair. a3 points to the next free word; a1 is the limit, a4 the
    // gas, a5 the instruction address minus the copy's lag. Keep prefix offsets
    // fixed.
    #define MONAD_VM_LEAD_SECTION(                                             \
        NAME, OP, SUFFIX, COPY, PAD, HEAD2, HEAD1, SIZE1)                      \
        asm(".pushsection .monad_vm_lead" #SUFFIX "." #NAME "." #OP            \
            ",\"ax\",@progbits\n"                                              \
            ".option push\n"                                                   \
            ".option norelax\n" MONAD_VM_BOOL_SECTION(NAME, OP, COPY, SUFFIX)  \
                MONAD_VM_SWAPN_SECTION(NAME, OP, COPY, SUFFIX)                 \
                    MONAD_VM_DUP_SECTION(NAME, OP, SUFFIX)                     \
                        MONAD_VM_SWAP1_SECTION(NAME, OP, COPY, SUFFIX) PAD     \
            "1:\ttail monad_vm_stack_overflow\n"                               \
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
    // The copies' heads, copy 0 first.
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
        MONAD_VM_LEAD_SECTION(NAME, OP, , 0, "", H2_0, H1_0, "32")             \
        MONAD_VM_LEAD_SECTION(NAME, OP, _1, 1, "", H2_1, H1_1, "32")           \
        MONAD_VM_LEAD_SECTION(NAME, OP, _2, 2, "\tnop\n", H2_2, H1_2, "28")    \
        MONAD_VM_LEAD_SECTION(NAME, OP, _3, 3, "\tnop\n", H2_3, H1_3, "28")    \
        MONAD_VM_LEAD_SECTION(NAME, OP, _4, 4, "\tnop\n", H2_4, H1_4, "28")    \
        MONAD_VM_LEAD_SECTION(NAME, OP, _5, 5, "\tnop\n", H2_5, H1_5, "28")    \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_LEAD_SECTION(                           \
            NAME, OP, _6, 6, "\tnop\n", H2_6, H1_6, "28"))

    // DUPn passes its source in a7. Copy it into the free slot at a3,
    // or let a fused follower read it directly.
    #define MONAD_VM_DUP_PLAIN(NAME, OP, SUFFIX)                               \
        "\tcsrs 0x813, a7\n"                                                   \
        "\taddi zero, a3, 32\n\taddi a3, a3, 32\n"                             \
        "\tj monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n" MONAD_VM_NOP5          \
        "\tnop\n"
    // The _OF_ table selects a prefix by the following opcode's hex value.
    // THEN enters dup_then; PLAIN copies the operand before the normal handler.
    #define MONAD_VM_DUP_THEN(NAME, OP, SUFFIX)                                \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_dup" #SUFFIX                   \
        "\n" MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n"
    // Copy DUPn's operand, then dispatch directly to the follower's PUSH
    // prefix. a5 already carries this copy's lag; no group advance is needed.
    // Keep each prefix at 40 bytes. Eager gas checks use the ordinary handler.
    #define MONAD_VM_DUP_PUSH1_AT(NAME, COPY, NEXT_BYTE, TARGET_OFFSET)        \
        "\tcsrs 0x813, a7\n\taddi zero, a3, 32\n\taddi a3, a3, 32\n"           \
        "\tbgeu a3, a1, 1f\n"                                                  \
        "\tlbu t1, " NEXT_BYTE "(a5)\n\tslli t0, t1, 12\n\tadd a7, a6, t0\n"   \
        "monad_vm_manual_jump_lag_dup_push1_" #NAME "_" #COPY                  \
        ": jr " TARGET_OFFSET "(a7)\n"                                         \
        "\tnop\n\tnop\n"
    #define MONAD_VM_DUP_PUSH1_COPY(NAME, OP)                                  \
        MONAD_VM_DUP_PUSH1_AT(NAME, 0, "2", "1332")
    #define MONAD_VM_DUP_PUSH1_COPY_1(NAME, OP)                                \
        MONAD_VM_DUP_PUSH1_AT(NAME, 1, "3", "2016")
    #define MONAD_VM_DUP_PUSH1_COPY_2(NAME, OP)                                \
        MONAD_VM_DUP_PUSH1_AT(NAME, 2, "4", "-1396")
    #define MONAD_VM_DUP_PUSH1_COPY_3(NAME, OP)                                \
        MONAD_VM_DUP_PUSH1_AT(NAME, 3, "5", "-712")
    #define MONAD_VM_DUP_PUSH1_COPY_4(NAME, OP)                                \
        MONAD_VM_DUP_PUSH1_AT(NAME, 4, "6", "-32")
    #define MONAD_VM_DUP_PUSH1_COPY_5(NAME, OP)                                \
        MONAD_VM_DUP_PUSH1_AT(NAME, 5, "7", "648")
    #define MONAD_VM_DUP_PUSH1(NAME, OP, SUFFIX)                               \
        MONAD_VM_LEAD_CAT(MONAD_VM_DUP_PUSH1_COPY, SUFFIX)(NAME, OP)
    #define MONAD_VM_DUP_PAIR_PUSH1(REV, NAME, OP)
    #define MONAD_VM_DUP_PUSH2_AT(NAME, COPY, NEXT_BYTE, TARGET_OFFSET)        \
        "\tcsrs 0x813, a7\n\taddi zero, a3, 32\n\taddi a3, a3, 32\n"           \
        "\tlbu t1, " NEXT_BYTE "(a5)\n\tslli t0, t1, 12\n\tadd a7, a6, t0\n"   \
        "monad_vm_manual_jump_lag_dup_push2_" #NAME "_" #COPY                  \
        ": jr " TARGET_OFFSET "(a7)\n"                                         \
        "\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_DUP_PUSH2_COPY(NAME, OP)                                  \
        MONAD_VM_DUP_PUSH2_AT(NAME, 0, "3", "1992")
    #define MONAD_VM_DUP_PUSH2_COPY_1(NAME, OP)                                \
        MONAD_VM_DUP_PUSH2_AT(NAME, 1, "4", "-1420")
    #define MONAD_VM_DUP_PUSH2_COPY_2(NAME, OP)                                \
        MONAD_VM_DUP_PUSH2_AT(NAME, 2, "5", "-736")
    #define MONAD_VM_DUP_PUSH2_COPY_3(NAME, OP)                                \
        MONAD_VM_DUP_PUSH2_AT(NAME, 3, "6", "-56")
    #define MONAD_VM_DUP_PUSH2_COPY_4(NAME, OP)                                \
        MONAD_VM_DUP_PUSH2_AT(NAME, 4, "7", "624")
    #define MONAD_VM_DUP_PUSH2_COPY_5(NAME, OP)                                \
        MONAD_VM_DUP_PUSH2_AT(NAME, 5, "8", "1308")
    #define MONAD_VM_DUP_PUSH2(NAME, OP, SUFFIX)                               \
        MONAD_VM_LEAD_CAT(MONAD_VM_DUP_PUSH2_COPY, SUFFIX)(NAME, OP)
    #define MONAD_VM_DUP_PAIR_PUSH2(REV, NAME, OP)
    #if !defined(MONAD_ZKVM_NO_DUP_FUSION)
    static_assert(
        push_prefix_offset(0, 1) == -1332 &&
        push_prefix_offset(1, 1) == -2016 && push_prefix_offset(2, 1) == 1396 &&
        push_prefix_offset(3, 1) == 712 && push_prefix_offset(4, 1) == 32 &&
        push_prefix_offset(5, 1) == -648 && push_prefix_offset(0, 2) == -1992 &&
        push_prefix_offset(1, 2) == 1420 && push_prefix_offset(2, 2) == 736 &&
        push_prefix_offset(3, 2) == 56 && push_prefix_offset(4, 2) == -624 &&
        push_prefix_offset(5, 2) == -1308);
    #endif
    #if !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        #define MONAD_VM_DUP_OF_60 ~, PUSH1 // PUSH1
        #define MONAD_VM_DUP_OF_61 ~, PUSH2 // PUSH2
    #endif
    #define MONAD_VM_DUP_OF_14 ~, THEN // EQ
    #define MONAD_VM_DUP_OF_15 ~, THEN // ISZERO
    #define MONAD_VM_DUP_OF_35 ~, THEN // CALLDATALOAD
    #define MONAD_VM_DUP_OF_01 ~, THEN // ADD
    #define MONAD_VM_DUP_OF_03 ~, THEN // SUB
    #define MONAD_VM_DUP_OF_10 ~, THEN // LT
    #define MONAD_VM_DUP_OF_11 ~, THEN // GT
    #define MONAD_VM_DUP_OF_16 ~, THEN // AND
    #define MONAD_VM_DUP_OF_51 ~, THEN // MLOAD
    #define MONAD_VM_DUP_OF_52 ~, THEN // MSTORE
    #define MONAD_VM_DUP_OF_90 ~, THEN // SWAP1
    #define MONAD_VM_DUP_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_DUP_, KIND)
    #define MONAD_VM_DUP_HEAD(NAME, OP, SUFFIX)                                \
        MONAD_VM_DUP_PICK(MONAD_VM_LEAD_KIND(MONAD_VM_DUP_OF_##OP, PLAIN, ~))( \
            NAME, OP, SUFFIX)
    // a7 carries the selected stack word's address or the comparison result.
    // The wrapper recovers the follower's bytecode address from a5 and LAG.
    #define MONAD_VM_SOURCE_PAIR_IN(                                           \
        FAMILY, HANDLER, SOURCE_TYPE, REV, NAME, OP, SUFFIX, LAG)              \
        extern "C"                                                             \
            [[gnu::section(".monad_vm_" #FAMILY "." #NAME "." #OP)]] void      \
                monad_vm_slot_##NAME##_##OP##_##FAMILY##SUFFIX(                \
                    runtime::Context &ctx,                                     \
                    MONAD_VM_DISPATCH_STATE_PARAM,                             \
                    uint256_t const *const stack_lower_bound,                  \
                    StackTop const stack_top,                                  \
                    int64_t const gas_remaining,                               \
                    uint8_t const *const instr_ptr,                            \
                    void const *const table_base,                              \
                    SOURCE_TYPE const source)                                  \
        {                                                                      \
            __attribute__((musttail)) return HANDLER<                          \
                0x##OP,                                                        \
                Lagged<EvmTraits<REV>, LAG, false>>(                           \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + (LAG),                                             \
                table_base,                                                    \
                source);                                                       \
        }
    #define MONAD_VM_DUP_THEN_IN(...)                                          \
        MONAD_VM_SOURCE_PAIR_IN(dup, dup_then, uint256_t const *, __VA_ARGS__)
    #define MONAD_VM_SWAPN_THEN_IN(...)                                        \
        MONAD_VM_SOURCE_PAIR_IN(swapn, swapn_then, uint256_t *, __VA_ARGS__)
    #define MONAD_VM_BOOL_THEN_IN(...)                                         \
        MONAD_VM_SOURCE_PAIR_IN(bool, comparison_then, uint64_t, __VA_ARGS__)
    #define MONAD_VM_BOOL_PLAIN(NAME, OP, COPY, SUFFIX)                        \
        "\tsd a7, -32(a3)\n\tsd zero, -24(a3)\n"                               \
        "\tsd zero, -16(a3)\n\tsd zero, -8(a3)\n"                              \
        "\tj monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n\tnop\n\tnop\n"
    #define MONAD_VM_BOOL_THEN(NAME, OP, COPY, SUFFIX)                         \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_bool" #SUFFIX "\n" MONAD_VM_NOP5
    // ISZERO keeps the inverted bit in a7. POP discards the unwritten slot.
    // On wrap, advance a5 by the group size after reading the next opcode.
    #define MONAD_VM_BOOL_ACTION_not "\tseqz a7, a7\n\taddi a4, a4, -3\n"
    #define MONAD_VM_BOOL_ACTION_pop "\taddi a3, a3, -32\n\taddi a4, a4, -2\n"
    #define MONAD_VM_BOOL_TARGET_not "-monad_vm_compare_distance"
    #define MONAD_VM_BOOL_TARGET_pop ""
    #define MONAD_VM_BOOL_NEXT(KIND, NAME, COPY, NEXT, STEP, OFFSET, PAD)      \
        MONAD_VM_BOOL_ACTION_##KIND                                            \
            "\tlbu t2, " NEXT "(a5)\n"                                         \
            "\tslli t2, t2, 12\n\tadd t3, a6, t2\n" STEP                       \
            "monad_vm_manual_jump_lag_bool_" #KIND "_" #NAME "_" #COPY         \
            ": jr " OFFSET MONAD_VM_BOOL_TARGET_##KIND "(t3)\n" PAD
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        #define MONAD_VM_BOOL_NOT MONAD_VM_BOOL_PLAIN
        #define MONAD_VM_BOOL_POP MONAD_VM_BOOL_PLAIN
    #else
        #define MONAD_VM_BOOL_NOT(NAME, OP, COPY, SUFFIX)                      \
            MONAD_VM_LEAD_CAT(MONAD_VM_NEXT_COPY_, COPY)(                      \
                MONAD_VM_BOOL_NEXT, not, NAME)
        #define MONAD_VM_BOOL_POP(NAME, OP, COPY, SUFFIX)                      \
            MONAD_VM_LEAD_CAT(MONAD_VM_NEXT_COPY_, COPY)(                      \
                MONAD_VM_BOOL_NEXT, pop, NAME)
    #endif
    // Select how the next opcode consumes the boolean in a7.
    // NOT/POP handle ISZERO/POP directly when gas checks are deferred;
    // THEN enters comparison_then. PLAIN writes the boolean to the stack.
    #define MONAD_VM_BOOL_OF_15 ~, NOT // ISZERO
    #define MONAD_VM_BOOL_OF_17 ~, THEN // OR
    #define MONAD_VM_BOOL_OF_50 ~, POP // POP
    #define MONAD_VM_BOOL_OF_61 ~, THEN // PUSH2
    #define MONAD_VM_BOOL_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_BOOL_, KIND)
    #define MONAD_VM_BOOL_HEAD(NAME, OP, COPY, SUFFIX)                         \
        MONAD_VM_BOOL_PICK(MONAD_VM_LEAD_KIND(                                 \
            MONAD_VM_BOOL_OF_##OP, PLAIN, ~))(NAME, OP, COPY, SUFFIX)
    #define MONAD_VM_DUP_PAIR_PLAIN(REV, NAME, OP)
    #define MONAD_VM_DUP_PAIR_THEN(REV, NAME, OP)                              \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, , 0)                               \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, _1, 1)                             \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, _2, 2)                             \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, _3, 3)                             \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, _4, 4)                             \
        MONAD_VM_DUP_THEN_IN(REV, NAME, OP, _5, 5)
    #define MONAD_VM_DUP_PAIR_PICK(KIND)                                       \
        MONAD_VM_LEAD_CAT(MONAD_VM_DUP_PAIR_, KIND)
    #if defined(MONAD_ZKVM_NO_DUP_FUSION)
        #define MONAD_VM_DUP_PAIR(REV, NAME, OP)
    #else
        #define MONAD_VM_DUP_PAIR(REV, NAME, OP)                               \
            MONAD_VM_DUP_PAIR_PICK(MONAD_VM_LEAD_KIND(                         \
                MONAD_VM_DUP_OF_##OP, PLAIN, ~))(REV, NAME, OP)

    #endif
    // a7 points to the deeper word selected by SWAP2–SWAP16. a3 points
    // one past the top, as it does on the ordinary handler entry.
    #define MONAD_VM_SWAPN_PLAIN(NAME, OP, COPY, SUFFIX)                       \
        "\taddi t1, a0, monad_vm_swap_scratch_offset\n"                        \
        "\taddi t4, a3, -32\n"                                                 \
        "\tcsrs 0x813, t4\n\taddi zero, t1, 32\n"                              \
        "\tcsrs 0x813, a7\n\taddi zero, t4, 32\n"                              \
        "\tcsrs 0x813, t1\n\taddi zero, a7, 32\n"                              \
        "\tj monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n\tnop\n"
    // The _OF_ table selects a prefix by the following opcode's hex value.
    // THEN calls swapn_then; POP handles SWAPn + POP directly in assembly
    // when gas checks are deferred. PLAIN swaps before the normal handler.
    #define MONAD_VM_SWAPN_THEN(NAME, OP, COPY, SUFFIX)                        \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_swapn" #SUFFIX                 \
        "\n" MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_SWAPN_OF_01 ~, THEN // ADD
    #define MONAD_VM_SWAPN_OF_03 ~, THEN // SUB
    #define MONAD_VM_SWAPN_OF_16 ~, THEN // AND
    #define MONAD_VM_SWAPN_OF_52 ~, THEN // MSTORE
    #define MONAD_VM_SWAPN_OF_50 ~, POP // POP
    #define MONAD_VM_SWAPN_OF_90 ~, THEN // SWAP1
    #define MONAD_VM_SWAPN_OF_91 ~, THEN // SWAP2
    #define MONAD_VM_SWAPN_OF_92 ~, THEN // SWAP3
    #define MONAD_VM_SWAPN_OF_93 ~, THEN // SWAP4
    #define MONAD_VM_SWAPN_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SWAPN_, KIND)
    #define MONAD_VM_SWAPN_HEAD(NAME, OP, COPY, SUFFIX)                        \
        MONAD_VM_SWAPN_PICK(MONAD_VM_LEAD_KIND(                                \
            MONAD_VM_SWAPN_OF_##OP, PLAIN, ~))(NAME, OP, COPY, SUFFIX)
    #define MONAD_VM_SWAPN_PAIR_PLAIN(REV, NAME, OP)
    #define MONAD_VM_SWAPN_PAIR_POP(REV, NAME, OP)
    #define MONAD_VM_SWAPN_PAIR_THEN(REV, NAME, OP)                            \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, , 0)                             \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _1, 1)                           \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _2, 2)                           \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _3, 3)                           \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _4, 4)                           \
        MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _5, 5)                           \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_SWAPN_THEN_IN(REV, NAME, OP, _6, 6))
    #define MONAD_VM_SWAPN_PAIR_PICK(KIND)                                     \
        MONAD_VM_LEAD_CAT(MONAD_VM_SWAPN_PAIR_, KIND)
    #if defined(MONAD_ZKVM_NO_SWAPN_FUSION)
        #define MONAD_VM_SWAPN_PAIR(REV, NAME, OP)
    #else
        #define MONAD_VM_SWAPN_PAIR(REV, NAME, OP)                             \
            MONAD_VM_SWAPN_PAIR_PICK(MONAD_VM_LEAD_KIND(                       \
                MONAD_VM_SWAPN_OF_##OP, PLAIN, ~))(REV, NAME, OP)
    #endif
    #define MONAD_VM_BOOL_PAIR_PLAIN(REV, NAME, OP)
    #define MONAD_VM_BOOL_PAIR_POP(REV, NAME, OP)
    #define MONAD_VM_BOOL_PAIR_THEN(REV, NAME, OP)                             \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, , 0)                              \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _1, 1)                            \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _2, 2)                            \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _3, 3)                            \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _4, 4)                            \
        MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _5, 5)                            \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_BOOL_THEN_IN(REV, NAME, OP, _6, 6))
    #define MONAD_VM_BOOL_PAIR_PICK(KIND)                                      \
        MONAD_VM_LEAD_CAT(MONAD_VM_BOOL_PAIR_, KIND)
    #define MONAD_VM_BOOL_PAIR_NOT(REV, NAME, OP)
    #if defined(MONAD_ZKVM_NO_COMPARISON_FUSION)
        #define MONAD_VM_BOOL_PAIR(REV, NAME, OP)
    #else
        #define MONAD_VM_BOOL_PAIR(REV, NAME, OP)                              \
            MONAD_VM_BOOL_PAIR_PICK(MONAD_VM_LEAD_KIND(                        \
                MONAD_VM_BOOL_OF_##OP, PLAIN, ~))(REV, NAME, OP)
    #endif
    // Save the second word in the spare slot at a3, then move both words
    // down together. ZisK DMA supports overlap; the spare slot exists even
    // at the EVM stack limit. Keep this prefix at 40 bytes.
    #define MONAD_VM_SWAP1_PLAIN(NAME, OP, COPY, SUFFIX)                       \
        "\taddi t4, a3, -64\n"                                                 \
        "\taddi t1, a3, -32\n"                                                 \
        "\tcsrs 0x813, t4\n"                                                   \
        "\taddi zero, a3, 32\n"                                                \
        "\tcsrs 0x813, t1\n"                                                   \
        "\taddi zero, t4, 64\n"                                                \
        "\tj monad_vm_slot_" #NAME "_" #OP #SUFFIX "\n\tnop\n\tnop\n\tnop\n"
    // POP discards the deeper word brought to the top. Only the old top
    // needs copying, to the second slot for SWAP1 or the slot in a7 for SWAPn.
    #define MONAD_VM_POP_MOVE_swap1                                            \
        "\taddi t4, a3, -32\n\tcsrs 0x813, a3\n\taddi zero, t4, 32\n"
    #define MONAD_VM_POP_MOVE_swapn "\tcsrs 0x813, a3\n\taddi zero, a7, 32\n"
    #define MONAD_VM_POP_PAD_swap1 ""
    #define MONAD_VM_POP_PAD_swapn "\tnop\n"
    #define MONAD_VM_SWAP_POP_AT(KIND, NAME, COPY, NEXT, STEP, OFFSET, PAD)    \
        "\taddi a3, a3, -32\n" MONAD_VM_POP_MOVE_##KIND                        \
            "\taddi a4, a4, -2\n"                                              \
            "\tlbu a7, " NEXT "(a5)\n"                                         \
            "\tslli a7, a7, 12\n"                                              \
            "\tadd t3, a6, a7\n" STEP "monad_vm_manual_jump_lag_" #KIND        \
            "_pop_" #NAME "_" #COPY ": jr " OFFSET                             \
            "(t3)\n" PAD MONAD_VM_POP_PAD_##KIND
    #if defined(MONAD_ZKVM_NO_DUP_FUSION)
        #if defined(MONAD_ZKVM_NO_SWAP1_PREFIX)
            #define MONAD_VM_POP_OFFSET(OFFSET) OFFSET "+8"
        #else
            #define MONAD_VM_POP_OFFSET(OFFSET) OFFSET
        #endif
        #define MONAD_VM_NEXT_COPY_0(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 0, "1", "", MONAD_VM_POP_OFFSET("576"), "\tnop\n")
        #define MONAD_VM_NEXT_COPY_1(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 1, "2", "", MONAD_VM_POP_OFFSET("1160"), "\tnop\n")
        #define MONAD_VM_NEXT_COPY_2(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 2, "3", "", MONAD_VM_POP_OFFSET("1744"), "\tnop\n")
        #define MONAD_VM_NEXT_COPY_3(EMIT, KIND, NAME)                         \
            EMIT(                                                              \
                KIND,                                                          \
                NAME,                                                          \
                3,                                                             \
                "4",                                                           \
                "",                                                            \
                MONAD_VM_POP_OFFSET("-1760"),                                  \
                "\tnop\n")
        #define MONAD_VM_NEXT_COPY_4(EMIT, KIND, NAME)                         \
            EMIT(                                                              \
                KIND,                                                          \
                NAME,                                                          \
                4,                                                             \
                "5",                                                           \
                "",                                                            \
                MONAD_VM_POP_OFFSET("-1176"),                                  \
                "\tnop\n")
        #define MONAD_VM_NEXT_COPY_5(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 5, "6", "", MONAD_VM_POP_OFFSET("-592"), "\tnop\n")
        #define MONAD_VM_NEXT_COPY_6(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 6, "7", MONAD_VM_STEP_GROUP, "0", "")
    #else
        #define MONAD_VM_NEXT_COPY_0(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 0, "1", "", "680", "\tnop\n")
        #define MONAD_VM_NEXT_COPY_1(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 1, "2", "", "1360", "\tnop\n")
        #define MONAD_VM_NEXT_COPY_2(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 2, "3", "", "2044", "\tnop\n")
        #define MONAD_VM_NEXT_COPY_3(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 3, "4", "", "-1368", "\tnop\n")
        #define MONAD_VM_NEXT_COPY_4(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 4, "5", "", "-684", "\tnop\n")
        #define MONAD_VM_NEXT_COPY_5(EMIT, KIND, NAME)                         \
            EMIT(KIND, NAME, 5, "6", MONAD_VM_STEP_GROUP, "0", "")
    #endif
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        #define MONAD_VM_SWAPN_POP(NAME, OP, COPY, SUFFIX)                     \
            MONAD_VM_SWAPN_PLAIN(NAME, OP, COPY, SUFFIX)
        // Let the ordinary POP handler check gas before popping.
        #define MONAD_VM_SWAP1_POP(NAME, OP, COPY, SUFFIX)                     \
            MONAD_VM_SWAP1_PLAIN(NAME, OP, COPY, SUFFIX)
    #else
        #define MONAD_VM_SWAPN_POP(NAME, OP, COPY, SUFFIX)                     \
            MONAD_VM_LEAD_CAT(MONAD_VM_NEXT_COPY_, COPY)(                      \
                MONAD_VM_SWAP_POP_AT, swapn, NAME)
        #define MONAD_VM_SWAP1_POP(NAME, OP, COPY, SUFFIX)                     \
            MONAD_VM_LEAD_CAT(MONAD_VM_NEXT_COPY_, COPY)(                      \
                MONAD_VM_SWAP_POP_AT, swap1, NAME)
    #endif
    #define MONAD_VM_SWAP1_JUMP(NAME, OP, COPY, SUFFIX)                        \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_swap1\n" MONAD_VM_NOP5         \
        "\tnop\n\tnop\n\tnop\n"
    // DUP2's and SWAP2's jump to their pair, compiled at the copy's lag.
    #define MONAD_VM_SWAP1_THEN(NAME, OP, COPY, SUFFIX)                        \
        "\ttail monad_vm_slot_" #NAME "_" #OP "_swap1" #SUFFIX                 \
        "\n" MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n"
    // Select the SWAP1 prefix by the following opcode's hexadecimal value.
    // POP handles the pair directly when gas checks are deferred; JUMP calls
    // swap1_jump and THEN calls swap1_then. PLAIN performs the ordinary swap.
    #define MONAD_VM_SWAP1_OF_50 ~, POP // POP
    #define MONAD_VM_SWAP1_OF_56 ~, JUMP // JUMP
    #define MONAD_VM_SWAP1_OF_81 ~, THEN // DUP2
    #define MONAD_VM_SWAP1_OF_91 ~, THEN // SWAP2
    #define MONAD_VM_SWAP1_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_, KIND)
    #define MONAD_VM_SWAP1_HEAD(NAME, OP, COPY, SUFFIX)                        \
        MONAD_VM_SWAP1_PICK(MONAD_VM_LEAD_KIND(                                \
            MONAD_VM_SWAP1_OF_##OP, PLAIN, ~))(NAME, OP, COPY, SUFFIX)
    // SWAP1 JUMP's pair, past the slots: the jump does not read a5.
    #define MONAD_VM_SWAP1_PAIR_PLAIN(REV, NAME, OP)
    #define MONAD_VM_SWAP1_PAIR_POP(REV, NAME, OP)
    #define MONAD_VM_SWAP1_PAIR_JUMP(REV, NAME, OP)                            \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _swap1, ".monad_vm_swap1." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return swap1_jump<                       \
                Lagged<EvmTraits<REV>, 0>>(                                    \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }
    // The pair DUP2's or SWAP2's head in copy SUFFIX jumps to: compiled with
    // instr_ptr LAG bytes ahead of a5.
    #define MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, SUFFIX, LAG)                 \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _swap1##SUFFIX, ".monad_vm_swap1." #NAME "." #OP)     \
        {                                                                      \
            __attribute__((musttail)) return swap1_then<                       \
                0x##OP,                                                        \
                Lagged<EvmTraits<REV>, LAG>>(                                  \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr + (LAG),                                             \
                table_base);                                                   \
        }
    #define MONAD_VM_SWAP1_PAIR_THEN(REV, NAME, OP)                            \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, , 0)                             \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _1, 1)                           \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _2, 2)                           \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _3, 3)                           \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _4, 4)                           \
        MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _5, 5)                           \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_SWAP1_THEN_IN(REV, NAME, OP, _6, 6))
    #define MONAD_VM_SWAP1_PAIR_PICK(KIND)                                     \
        MONAD_VM_LEAD_CAT(MONAD_VM_SWAP1_PAIR_, KIND)
    #if defined(MONAD_ZKVM_NO_SWAP1_PREFIX)
        #define MONAD_VM_SWAP1_PAIR(REV, NAME, OP)
    #else
        #define MONAD_VM_SWAP1_PAIR(REV, NAME, OP)                             \
            MONAD_VM_SWAP1_PAIR_PICK(MONAD_VM_LEAD_KIND(                       \
                MONAD_VM_SWAP1_OF_##OP, PLAIN, ~))(REV, NAME, OP)
    #endif

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
    #define MONAD_VM_STEP_GROUP "\taddi a5, a5, " MONAD_VM_GROUP_SIZE "\n"
    #define MONAD_VM_HEAD1_PUSH(IMM, STEP)                                     \
        "\tlbu t3, " IMM "(a5)\n3:\n" MONAD_VM_PUSH_T3 STEP
    #define MONAD_VM_HEAD2_PUSH(HIGH, LOW, STEP, PAD)                          \
        MONAD_VM_PUSH2_READ_AT("1b", HIGH, LOW) STEP "\tj 3f\n" PAD
    #define MONAD_VM_NOP5 "\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_HEAD_TO(TARGET, PAD) "\ttail " TARGET "\n" PAD
    // The first copies read PUSH immediates across a group boundary.
    #define MONAD_VM_PLAIN1_0                                                  \
        MONAD_VM_HEAD1_PUSH(MONAD_VM_GROUP_SIZE "-1", MONAD_VM_STEP_GROUP)
    #define MONAD_VM_PLAIN1_1                                                  \
        MONAD_VM_HEAD1_PUSH(MONAD_VM_GROUP_SIZE, MONAD_VM_STEP_GROUP)
    #define MONAD_VM_PLAIN1_2 MONAD_VM_HEAD1_PUSH("1", "")
    #define MONAD_VM_PLAIN1_3 MONAD_VM_HEAD1_PUSH("2", "")
    #define MONAD_VM_PLAIN1_4 MONAD_VM_HEAD1_PUSH("3", "")
    #define MONAD_VM_PLAIN1_5 MONAD_VM_HEAD1_PUSH("4", "")
    #define MONAD_VM_PLAIN2_0                                                  \
        MONAD_VM_HEAD2_PUSH(                                                   \
            MONAD_VM_GROUP_SIZE "-2", MONAD_VM_GROUP_SIZE "-1", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_1                                                  \
        MONAD_VM_HEAD2_PUSH(                                                   \
            MONAD_VM_GROUP_SIZE "-1", MONAD_VM_GROUP_SIZE, "", "\tnop\n")
    #define MONAD_VM_PLAIN2_2                                                  \
        MONAD_VM_HEAD2_PUSH(                                                   \
            MONAD_VM_GROUP_SIZE,                                               \
            MONAD_VM_GROUP_SIZE "+1",                                          \
            MONAD_VM_STEP_GROUP,                                               \
            "")
    #define MONAD_VM_PLAIN2_3 MONAD_VM_HEAD2_PUSH("1", "2", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_4 MONAD_VM_HEAD2_PUSH("2", "3", "", "\tnop\n")
    #define MONAD_VM_PLAIN2_5 MONAD_VM_HEAD2_PUSH("3", "4", "", "\tnop\n")
    #define MONAD_VM_PLAIN1_6 MONAD_VM_HEAD1_PUSH("5", "")
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
    #define MONAD_VM_PAIRS1(REV, NAME, OP, ...)                                \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, , lag_count - 2, __VA_ARGS__)   \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _1, lag_count - 1, __VA_ARGS__) \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _2, 0, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _3, 1, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _4, 2, __VA_ARGS__)             \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _5, 3, __VA_ARGS__)             \
        MONAD_VM_SEVENTH_COPY(                                                 \
            MONAD_VM_PAIR_IN(REV, NAME, OP, push1, _6, 4, __VA_ARGS__))
    #define MONAD_VM_PAIRS2(REV, NAME, OP)                                     \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, , lag_count - 3)                \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _1, lag_count - 2)              \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _2, lag_count - 1)              \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _3, 0)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _4, 1)                          \
        MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _5, 2)                          \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_PAIR_IN(REV, NAME, OP, push2, _6, 3))
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
            sizeof(uint256_t) == 32 &&                                         \
            (fuse_dup                                                          \
                 ? (slot_handler_offset == (fuse_swap1 ? 1512 : 1472) +        \
                                               swapn_prefix_bytes +            \
                                               comparison_prefix_bytes &&      \
                    lag_offset(1) == 680 && lag_offset(2) == 1360 &&           \
                    lag_offset(3) == 2044 && lag_offset(4) == -1368 &&         \
                    lag_offset(5) == -684)                                     \
                 : (!fuse_swap1 ||                                             \
                    (slot_handler_offset == 1864 + swapn_prefix_bytes +        \
                                                comparison_prefix_bytes &&     \
                     lag_offset(1) == 576 && lag_offset(2) == 1160 &&          \
                     lag_offset(3) == 1744 && lag_offset(4) == -1760 &&        \
                     lag_offset(5) == -1176 && lag_offset(6) == -592))) &&     \
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
        MONAD_VM_PUSH2_IN(                                                     \
            NAME,                                                              \
            OP,                                                                \
            ,                                                                  \
            MONAD_VM_GROUP_SIZE "-2",                                          \
            MONAD_VM_GROUP_SIZE "-1",                                          \
            MONAD_VM_STEP_GROUP)                                               \
        MONAD_VM_PUSH2_IN(                                                     \
            NAME,                                                              \
            OP,                                                                \
            _1,                                                                \
            MONAD_VM_GROUP_SIZE "-1",                                          \
            MONAD_VM_GROUP_SIZE,                                               \
            MONAD_VM_STEP_GROUP)                                               \
        MONAD_VM_PUSH2_IN(                                                     \
            NAME,                                                              \
            OP,                                                                \
            _2,                                                                \
            MONAD_VM_GROUP_SIZE,                                               \
            MONAD_VM_GROUP_SIZE "+1",                                          \
            MONAD_VM_STEP_GROUP)                                               \
        MONAD_VM_PUSH2_IN(NAME, OP, _3, "1", "2", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _4, "2", "3", "")                          \
        MONAD_VM_PUSH2_IN(NAME, OP, _5, "3", "4", "")                          \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_PUSH2_IN(NAME, OP, _6, "4", "5", ""))   \
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
        MONAD_VM_COPY(REV, NAME, OP, _5, ".monad_vm_slot5", 5)                 \
        MONAD_VM_SEVENTH_COPY(                                                 \
            MONAD_VM_COPY(REV, NAME, OP, _6, ".monad_vm_slot6", 6))

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
        MONAD_VM_RELAY_IN(                                                     \
            NAME, OP, _5, ".monad_vm_slot5", "\taddi a5, a5, 5\n")             \
        MONAD_VM_SEVENTH_COPY(MONAD_VM_RELAY_IN(                               \
            NAME, OP, _6, ".monad_vm_slot6", "\taddi a5, a5, 6\n"))
    #define MONAD_VM_RELAY_OF_04 ~, RELAY // DIV
    #define MONAD_VM_RELAY_OF_06 ~, RELAY // MOD
    #define MONAD_VM_RELAY_OF_08 ~, RELAY // ADDMOD
    #define MONAD_VM_RELAY_OF_0a ~, RELAY // EXP
    // These bodies exceed a copy region with the current runtime inlining.
    #define MONAD_VM_RELAY_OF_37 ~, RELAY // CALLDATACOPY
    #define MONAD_VM_RELAY_OF_39 ~, RELAY // CODECOPY
    #define MONAD_VM_RELAY_OF_3e ~, RELAY // RETURNDATACOPY
    #if !defined(MONAD_ZKVM_NO_SWAPN_FUSION) ||                                \
        (defined(MONAD_ZKVM_NO_DUP_FUSION) &&                                  \
         !defined(MONAD_ZKVM_NO_SWAP1_PREFIX))
        #define MONAD_VM_RELAY_OF_20 ~, RELAY // SHA3
    #endif
    #if defined(MONAD_ZKVM_NO_DUP_FUSION) &&                                   \
        !defined(MONAD_ZKVM_NO_SWAP1_PREFIX) &&                                \
        !defined(MONAD_ZKVM_NO_SWAPN_FUSION) &&                                \
        !defined(MONAD_ZKVM_NO_COMPARISON_FUSION)
        // Seven copies with all three prefixes leave too little room for
        // MSTORE8.
        #define MONAD_VM_RELAY_OF_53 ~, RELAY // MSTORE8
    #endif
    #define MONAD_VM_RELAY_OF_55 ~, RELAY // SSTORE
    #define MONAD_VM_RELAY_OF_5e ~, RELAY // MCOPY
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE) ||                          \
        (defined(MONAD_ZKVM_NO_DUP_FUSION) &&                                  \
         (!defined(MONAD_ZKVM_NO_COMPARISON_FUSION) ||                         \
          !defined(MONAD_ZKVM_NO_SWAPN_FUSION)))
        // Seven copies need a relay when either comparison or SWAPn prefixes
        // are present.
        #define MONAD_VM_RELAY_OF_80 ~, RELAY // DUP1
    #endif
    #define MONAD_VM_SLOT_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_SLOT_, KIND)

    #define MONAD_VM_SLOT(REV, NAME, OP)                                       \
        MONAD_VM_LEAD(REV, NAME, OP)                                           \
        MONAD_VM_BOOL_PAIR(REV, NAME, OP)                                      \
        MONAD_VM_SWAPN_PAIR(REV, NAME, OP)                                     \
        MONAD_VM_DUP_PAIR(REV, NAME, OP)                                       \
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

    MONAD_VM_SLOTS(EvmRevision::Berlin, 08)
    MONAD_VM_SLOTS(EvmRevision::London, 09)
    MONAD_VM_SLOTS(EvmRevision::Paris, 10)
    MONAD_VM_SLOTS(EvmRevision::Shanghai, 11)
    MONAD_VM_SLOTS(EvmRevision::Cancun, 12)
    MONAD_VM_SLOTS(EvmRevision::Prague, 13)
    MONAD_VM_SLOTS(EvmRevision::Osaka, 14)
    MONAD_VM_SLOTS(EvmRevision::Amsterdam, 15)

    #undef MONAD_VM_SOURCE_PAIR_IN
    #undef MONAD_VM_SWAPN_SECTION
    #undef MONAD_VM_SWAPN_THEN_IN
    #undef MONAD_VM_SWAPN_PLAIN
    #undef MONAD_VM_SWAPN_THEN
    #undef MONAD_VM_SWAPN_OF_01
    #undef MONAD_VM_SWAPN_OF_03
    #undef MONAD_VM_SWAPN_OF_16
    #undef MONAD_VM_SWAPN_OF_52
    #undef MONAD_VM_SWAPN_OF_50
    #undef MONAD_VM_SWAPN_OF_90
    #undef MONAD_VM_SWAPN_OF_91
    #undef MONAD_VM_SWAPN_OF_92
    #undef MONAD_VM_SWAPN_OF_93
    #undef MONAD_VM_SWAPN_PICK
    #undef MONAD_VM_SWAPN_HEAD
    #undef MONAD_VM_SWAPN_PAIR_PLAIN
    #undef MONAD_VM_SWAPN_PAIR_POP
    #undef MONAD_VM_SWAPN_PAIR_THEN
    #undef MONAD_VM_SWAPN_PAIR_PICK
    #undef MONAD_VM_SWAPN_PAIR
    #undef MONAD_VM_POP_MOVE_swap1
    #undef MONAD_VM_POP_MOVE_swapn
    #undef MONAD_VM_POP_PAD_swap1
    #undef MONAD_VM_POP_PAD_swapn
    #undef MONAD_VM_POP_OFFSET
    #undef MONAD_VM_SWAPN_POP
    #undef MONAD_VM_BOOL_THEN_IN
    #undef MONAD_VM_BOOL_PLAIN
    #undef MONAD_VM_BOOL_THEN
    #undef MONAD_VM_BOOL_ACTION_not
    #undef MONAD_VM_BOOL_ACTION_pop
    #undef MONAD_VM_BOOL_TARGET_not
    #undef MONAD_VM_BOOL_TARGET_pop
    #undef MONAD_VM_BOOL_NEXT
    #undef MONAD_VM_BOOL_NOT
    #undef MONAD_VM_BOOL_POP
    #undef MONAD_VM_BOOL_OF_15
    #undef MONAD_VM_BOOL_OF_17
    #undef MONAD_VM_BOOL_OF_50
    #undef MONAD_VM_BOOL_OF_61
    #undef MONAD_VM_BOOL_PICK
    #undef MONAD_VM_BOOL_SECTION
    #undef MONAD_VM_BOOL_HEAD
    #undef MONAD_VM_BOOL_PAIR_PLAIN
    #undef MONAD_VM_BOOL_PAIR_POP
    #undef MONAD_VM_BOOL_PAIR_THEN
    #undef MONAD_VM_BOOL_PAIR_PICK
    #undef MONAD_VM_BOOL_PAIR_NOT
    #undef MONAD_VM_BOOL_PAIR
    #undef MONAD_VM_SLOTS
    #undef MONAD_VM_SLOTS_16
    #undef MONAD_VM_SLOT
    #undef MONAD_VM_RELAY_OF_80
    #undef MONAD_VM_SLOT_PICK
    #undef MONAD_VM_RELAY_OF_37
    #undef MONAD_VM_RELAY_OF_39
    #undef MONAD_VM_RELAY_OF_3e
    #undef MONAD_VM_RELAY_OF_53
    #undef MONAD_VM_RELAY_OF_55
    #undef MONAD_VM_RELAY_OF_5e
    #undef MONAD_VM_RELAY_OF_0a
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
    #undef MONAD_VM_STEP_GROUP
    #undef MONAD_VM_PUSH_T3
    #undef MONAD_VM_PUSH2_READ_AT
    #undef MONAD_VM_SWAP1_PAIR
    #undef MONAD_VM_SWAP1_PAIR_PICK
    #undef MONAD_VM_SWAP1_PAIR_THEN
    #undef MONAD_VM_SWAP1_THEN_IN
    #undef MONAD_VM_SWAP1_PAIR_JUMP
    #undef MONAD_VM_SWAP1_PAIR_POP
    #undef MONAD_VM_SWAP1_PAIR_PLAIN
    #undef MONAD_VM_SWAP1_HEAD
    #undef MONAD_VM_SWAP1_PICK
    #undef MONAD_VM_SWAP1_OF_91
    #undef MONAD_VM_SWAP1_OF_81
    #undef MONAD_VM_SWAP1_OF_56
    #undef MONAD_VM_SWAP1_OF_50
    #undef MONAD_VM_SWAP1_JUMP
    #undef MONAD_VM_SWAP1_THEN
    #undef MONAD_VM_SWAP1_POP
    #undef MONAD_VM_NEXT_COPY_5
    #undef MONAD_VM_NEXT_COPY_4
    #undef MONAD_VM_NEXT_COPY_3
    #undef MONAD_VM_NEXT_COPY_2
    #undef MONAD_VM_NEXT_COPY_1
    #undef MONAD_VM_NEXT_COPY_0
    #undef MONAD_VM_DUP_PLAIN
    #undef MONAD_VM_DUP_THEN
    #undef MONAD_VM_DUP_PUSH1_AT
    #undef MONAD_VM_DUP_PUSH1
    #undef MONAD_VM_DUP_PAIR_PUSH1
    #undef MONAD_VM_DUP_PUSH1_COPY
    #undef MONAD_VM_DUP_PUSH1_COPY_1
    #undef MONAD_VM_DUP_PUSH1_COPY_2
    #undef MONAD_VM_DUP_PUSH1_COPY_3
    #undef MONAD_VM_DUP_PUSH1_COPY_4
    #undef MONAD_VM_DUP_PUSH1_COPY_5
    #undef MONAD_VM_DUP_PUSH2_AT
    #undef MONAD_VM_DUP_PUSH2
    #undef MONAD_VM_DUP_PAIR_PUSH2
    #undef MONAD_VM_DUP_PUSH2_COPY
    #undef MONAD_VM_DUP_PUSH2_COPY_1
    #undef MONAD_VM_DUP_PUSH2_COPY_2
    #undef MONAD_VM_DUP_PUSH2_COPY_3
    #undef MONAD_VM_DUP_PUSH2_COPY_4
    #undef MONAD_VM_DUP_PUSH2_COPY_5
    #undef MONAD_VM_DUP_OF_60
    #undef MONAD_VM_DUP_OF_61
    #undef MONAD_VM_DUP_OF_14
    #undef MONAD_VM_DUP_OF_15
    #undef MONAD_VM_DUP_OF_35
    #undef MONAD_VM_DUP_OF_01
    #undef MONAD_VM_DUP_OF_03
    #undef MONAD_VM_DUP_OF_10
    #undef MONAD_VM_DUP_OF_11
    #undef MONAD_VM_DUP_OF_16
    #undef MONAD_VM_DUP_OF_51
    #undef MONAD_VM_DUP_OF_52
    #undef MONAD_VM_DUP_OF_90
    #undef MONAD_VM_DUP_PICK
    #undef MONAD_VM_DUP_HEAD
    #undef MONAD_VM_DUP_THEN_IN
    #undef MONAD_VM_DUP_PAIR_PLAIN
    #undef MONAD_VM_DUP_PAIR_THEN
    #undef MONAD_VM_DUP_PAIR_PICK
    #undef MONAD_VM_DUP_PAIR
    #undef MONAD_VM_SWAP_POP_AT
    #undef MONAD_VM_SWAP1_PLAIN
    #undef MONAD_VM_DUP_SECTION
    #undef MONAD_VM_SEVENTH_COPY
    #undef MONAD_VM_GROUP_SIZE
    #undef MONAD_VM_PLAIN1_6
    #undef MONAD_VM_PLAIN2_6
    #undef MONAD_VM_NEXT_COPY_6
    #undef MONAD_VM_RELAY_OF_20
    #undef MONAD_VM_LEADS
    #undef MONAD_VM_SWAP1_SECTION
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
        ctx.stack_limit =
            stack_ptr + runtime::EvmStackAllocatorMeta::max_stack_height;

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
