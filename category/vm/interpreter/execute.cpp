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
    // Each 1-KiB slot begins with [overflow exit: 8][PUSH2: 24][PUSH1: 32].
    // Ordinary dispatch skips all 64 bytes. PUSH1/PUSH2 enter their own
    // prefix in the follower's slot, before executing the pending push.
    // Ordinary PUSH2 prefixes decode two bytes, then reuse PUSH1's stores.
    // Fused prefixes jump to a pair; PUSH2 JUMP/JUMPI pairs live in that slot.
    // a3 holds StackTop's next free slot, a1 the stack limit, a4 the gas,
    // and a5 the PUSH instruction pointer. Disable relaxation to keep offsets
    // fixed, and use musttail so handlers do not acquire a call frame.
    #define MONAD_VM_LEAD_ASM(NAME, OP, HEAD2, HEAD1)                          \
        asm(".pushsection .monad_vm_lead." #NAME "." #OP ",\"ax\",@progbits\n" \
            ".option push\n"                                                   \
            ".option norelax\n"                                                \
            "1:\ttail monad_vm_stack_overflow\n"                               \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead2, @function\n"         \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead2, 24\n"                \
            "monad_vm_slot_" #NAME "_" #OP "_lead2:\n" HEAD2                   \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead, @function\n"          \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead, 32\n"                 \
            "monad_vm_slot_" #NAME "_" #OP "_lead:\n" HEAD1 ".option pop\n"    \
            ".popsection");

    // PUSH2's stack test, leaving through EXIT, and its immediate in t3.
    #define MONAD_VM_PUSH2_READ(EXIT)                                          \
        "\tbgeu a3, a1, " EXIT "\n"                                            \
        "\tlbu t3, 1(a5)\n"                                                    \
        "\tlbu t4, 2(a5)\n"                                                    \
        "\tpackh t3, t4, t3\n"                                                 \
        "\taddi a5, a5, 1\n"
    // The push of t3 and the rest of PUSH1.
    #define MONAD_VM_PUSH_T3                                                   \
        "\tsd t3, 0(a3)\n"                                                     \
        "\tsd zero, 8(a3)\n"                                                   \
        "\tsd zero, 16(a3)\n"                                                  \
        "\tsd zero, 24(a3)\n"                                                  \
        "\taddi a3, a3, 32\n"                                                  \
        "\taddi a4, a4, -3\n"                                                  \
        "\taddi a5, a5, 2\n"
    #define MONAD_VM_HEAD2_PUSH MONAD_VM_PUSH2_READ("1b") "\tj 3f\n"
    #define MONAD_VM_HEAD1_PUSH "\tlbu t3, 1(a5)\n3:\n" MONAD_VM_PUSH_T3
    #define MONAD_VM_HEAD2_JUMP(NAME, OP)                                      \
        "\tj monad_vm_slot_" #NAME "_" #OP "_push2\n"                          \
        "\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n"
    #define MONAD_VM_HEAD1_JUMP(NAME, OP)                                      \
        "\tj monad_vm_slot_" #NAME "_" #OP "_push1\n"                          \
        "\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n\tnop\n"

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

    #define MONAD_VM_LEAD_PUSH(REV, NAME, OP)                                  \
        static_assert(                                                         \
            compiler::opcode_table<EvmTraits<REV>>[PUSH1].min_gas == 3 &&      \
            compiler::opcode_table<EvmTraits<REV>>[PUSH2].min_gas == 3 &&      \
            sizeof(uint256_t) == 32 && slot_prefix_size == 64 &&               \
            push1_prefix_offset == 32 && push2_prefix_offset == 56);           \
        MONAD_VM_LEAD_ASM(NAME, OP, MONAD_VM_HEAD2_PUSH, MONAD_VM_HEAD1_PUSH)

    #define MONAD_VM_LEAD_PAIR(REV, NAME, OP)                                  \
        MONAD_VM_LEAD_ASM(                                                     \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_HEAD2_JUMP(NAME, OP),                                     \
            MONAD_VM_HEAD1_JUMP(NAME, OP))                                     \
        asm(".pushsection .monad_vm_push2." #NAME "." #OP                      \
            ",\"ax\",@progbits\n"                                              \
            ".option push\n"                                                   \
            ".option norelax\n"                                                \
            ".type monad_vm_slot_" #NAME "_" #OP "_push2, @function\n"         \
            "monad_vm_slot_" #NAME "_" #OP                                     \
            "_push2:\n" MONAD_VM_PUSH2_READ("2f") MONAD_VM_PUSH_T3             \
            "\tj monad_vm_slot_" #NAME "_" #OP "\n"                            \
            "2:\ttail monad_vm_stack_overflow\n"                               \
            ".size monad_vm_slot_" #NAME "_" #OP "_push2, . - "                \
            "monad_vm_slot_" #NAME "_" #OP "_push2\n"                          \
            ".option pop\n"                                                    \
            ".popsection");                                                    \
        extern "C" [[gnu::section(".monad_vm_slot." #NAME "." #OP)]] void      \
            monad_vm_slot_##NAME##_##OP(                                       \
                runtime::Context &,                                            \
                MONAD_VM_DISPATCH_STATE_TYPE,                                  \
                uint256_t const *,                                             \
                StackTop,                                                      \
                int64_t,                                                       \
                uint8_t const *,                                               \
                void const *);                                                 \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _push1, ".monad_vm_push1." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return push1_then<                       \
                0x##OP,                                                        \
                EvmTraits<REV>,                                                \
                monad_vm_slot_##NAME##_##OP>(                                  \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }

    // Both prefixes select a fusion: PUSH1 and PUSH2 with MLOAD/MSTORE.
    #define MONAD_VM_LEAD_PAIRS(REV, NAME, OP)                                 \
        MONAD_VM_LEAD_ASM(                                                     \
            NAME,                                                              \
            OP,                                                                \
            MONAD_VM_HEAD2_JUMP(NAME, OP),                                     \
            MONAD_VM_HEAD1_JUMP(NAME, OP))                                     \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _push1, ".monad_vm_push1." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return push1_then<                       \
                0x##OP,                                                        \
                EvmTraits<REV>>(                                               \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }                                                                      \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _push2, ".monad_vm_push2." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return push2_then<                       \
                0x##OP,                                                        \
                EvmTraits<REV>>(                                               \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }

    #define MONAD_VM_LEAD_TWIN(REV, NAME, OP)                                  \
        MONAD_VM_LEAD_ASM(                                                     \
            NAME, OP, MONAD_VM_HEAD2_JUMP(NAME, OP), MONAD_VM_HEAD1_PUSH)      \
        MONAD_VM_HANDLER_DECL(                                                 \
            NAME##_##OP, _push2, ".monad_vm_push2." #NAME "." #OP)             \
        {                                                                      \
            __attribute__((musttail)) return push2_then<                       \
                0x##OP,                                                        \
                EvmTraits<REV>>(                                               \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }

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

    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
    // Extra gas checks make DUP1 exceed the space left by both prefixes.
    // Keep its body outside the slot in this verification mode only.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void checked_dup1(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr, void const *table_base)
    {
        __attribute__((musttail)) return dup<1, traits>(
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr,
            table_base);
    }

        #define MONAD_VM_SLOT_HANDLER(REV, OP)                                 \
            (0x##OP == 0x80 ? &checked_dup1<EvmTraits<REV>>                    \
                            : instruction_table<EvmTraits<REV>>[0x##OP])
    #else
        #define MONAD_VM_SLOT_HANDLER(REV, OP)                                 \
            instruction_table<EvmTraits<REV>>[0x##OP]
    #endif

    #define MONAD_VM_SLOT(REV, NAME, OP)                                       \
        MONAD_VM_LEAD(REV, NAME, OP)                                           \
        extern "C" [[gnu::section(".monad_vm_slot." #NAME "." #OP)]] void      \
            monad_vm_slot_##NAME##_##OP(                                       \
                runtime::Context &ctx,                                         \
                MONAD_VM_DISPATCH_STATE_PARAM,                                 \
                uint256_t const *const stack_lower_bound,                      \
                StackTop const stack_top,                                      \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const table_base)                                  \
        {                                                                      \
            constexpr InstrEval handler = MONAD_VM_SLOT_HANDLER(REV, OP);      \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                table_base);                                                   \
        }

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
    #undef MONAD_VM_SLOT_HANDLER
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
    #undef MONAD_VM_HANDLER_DECL
    #undef MONAD_VM_HEAD1_JUMP
    #undef MONAD_VM_HEAD2_JUMP
    #undef MONAD_VM_HEAD1_PUSH
    #undef MONAD_VM_HEAD2_PUSH
    #undef MONAD_VM_PUSH_T3
    #undef MONAD_VM_PUSH2_READ
    #undef MONAD_VM_LEAD_ASM
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
            void const *table_base;
            if constexpr (has_slots<traits>) {
                table_base = monad_vm_slots +
                             ((static_cast<unsigned>(EvmRevision::Amsterdam) -
                               static_cast<unsigned>(traits::evm_rev()))
                              << 8 << slot_shift) +
                             slot_prefix_size;
            }
            else {
                table_base = instruction_table<traits>.data();
            }
            InstrEval const first =
                dispatch_table<traits>(table_base)[*instr_ptr];
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
