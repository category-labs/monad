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
    // Slots already provide calculable handler addresses. Their PUSH1 prefix
    // adds a second entry, 32 bytes before the normal handler. PUSH1 has not
    // executed when it enters here: most prefixes push its immediate, charge
    // gas and fall into the handler. Fused prefixes jump to push1_then<OP>.
    // Ordinary opcode dispatch skips the prefix. The ABI carries StackTop's
    // next free slot in a3, gas in a4, and the PUSH1 instruction pointer in a5.
    // Keep musttail: a normal call can give the inlined handler a stack frame.
    #define MONAD_VM_LEAD_PUSH(REV, NAME, OP)                                  \
        static_assert(                                                         \
            compiler::opcode_table<EvmTraits<REV>>[PUSH1].min_gas == 3 &&      \
            sizeof(uint256_t) == 32 && push1_prefix_size == 32);               \
        asm(".pushsection .monad_vm_lead." #NAME "." #OP ",\"ax\",@progbits\n" \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead, @function\n"          \
            "monad_vm_slot_" #NAME "_" #OP "_lead:\n"                          \
            "\tlbu t3, 1(a5)\n"                                                \
            "\tsd t3, 0(a3)\n"                                                 \
            "\tsd zero, 8(a3)\n"                                               \
            "\tsd zero, 16(a3)\n"                                              \
            "\tsd zero, 24(a3)\n"                                              \
            "\taddi a3, a3, 32\n"                                              \
            "\taddi a4, a4, -3\n"                                              \
            "\taddi a5, a5, 2\n"                                               \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead, . - "                 \
            "monad_vm_slot_" #NAME "_" #OP "_lead\n"                           \
            ".popsection");

    #define MONAD_VM_LEAD_PAIR(REV, NAME, OP)                                  \
        asm(".pushsection .monad_vm_lead." #NAME "." #OP ",\"ax\",@progbits\n" \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead, @function\n"          \
            "monad_vm_slot_" #NAME "_" #OP "_lead:\n"                          \
            "\tj monad_vm_slot_" #NAME "_" #OP "_push1\n"                      \
            ".size monad_vm_slot_" #NAME "_" #OP "_lead, . - "                 \
            "monad_vm_slot_" #NAME "_" #OP "_lead\n"                           \
            ".popsection");                                                    \
        extern "C" [[gnu::section(".monad_vm_push1." #NAME "." #OP)]] void     \
            monad_vm_slot_##NAME##_##OP##_push1(                               \
                runtime::Context &ctx,                                         \
                MONAD_VM_DISPATCH_STATE_PARAM,                                 \
                uint256_t const *const stack_lower_bound,                      \
                StackTop const stack_top,                                      \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const table_base)                                  \
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
        }

    // These opcodes use a fused PUSH1 pair; all others use the ordinary
    // PUSH1 prefix. The suffix is the opcode in hexadecimal.
    #define MONAD_VM_PUSH1_PAIR_01 ~, PAIR // ADD
    #define MONAD_VM_PUSH1_PAIR_1b ~, PAIR // SHL
    #define MONAD_VM_PUSH1_PAIR_1c ~, PAIR // SHR
    #define MONAD_VM_PUSH1_PAIR_1d ~, PAIR // SAR
    #define MONAD_VM_PUSH1_PAIR_51 ~, PAIR // MLOAD
    #define MONAD_VM_PUSH1_PAIR_52 ~, PAIR // MSTORE
    #define MONAD_VM_PUSH1_PAIR_60 ~, PAIR // PUSH1
    #define MONAD_VM_LEAD_SECOND(A, B, ...) B
    #define MONAD_VM_LEAD_KIND(...) MONAD_VM_LEAD_SECOND(__VA_ARGS__)
    #define MONAD_VM_LEAD_CAT(A, B) A##B
    #define MONAD_VM_LEAD_PICK(KIND) MONAD_VM_LEAD_CAT(MONAD_VM_LEAD_, KIND)
    #define MONAD_VM_LEAD(REV, NAME, OP)                                       \
        MONAD_VM_LEAD_PICK(MONAD_VM_LEAD_KIND(                                 \
            MONAD_VM_PUSH1_PAIR_##OP, PUSH, ~))(REV, NAME, OP)

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
            constexpr InstrEval handler =                                      \
                instruction_table<EvmTraits<REV>>[0x##OP];                     \
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
    #undef MONAD_VM_LEAD
    #undef MONAD_VM_LEAD_PICK
    #undef MONAD_VM_LEAD_CAT
    #undef MONAD_VM_LEAD_KIND
    #undef MONAD_VM_LEAD_SECOND
    #undef MONAD_VM_PUSH1_PAIR_60
    #undef MONAD_VM_PUSH1_PAIR_52
    #undef MONAD_VM_PUSH1_PAIR_51
    #undef MONAD_VM_PUSH1_PAIR_1d
    #undef MONAD_VM_PUSH1_PAIR_1c
    #undef MONAD_VM_PUSH1_PAIR_1b
    #undef MONAD_VM_PUSH1_PAIR_01
    #undef MONAD_VM_LEAD_PAIR
    #undef MONAD_VM_LEAD_PUSH
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
                             push1_prefix_size;
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
