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
// call, within a jal's reach.
extern "C" unsigned char const monad_vm_slots[];
#endif

namespace monad::vm::interpreter
{
#if defined(MONAD_ZKVM_ZISK)
    // One slot per revision and opcode: the opcode's handler, compiled into
    // it. The section's name tells the linker script where to put it (the
    // revision in two decimal digits, the opcode in two hexadecimal ones);
    // an alignment attribute would not do it, since the assembler pads to it
    // with nops the linker relaxes away only after placing the sections. The
    // handler is reached by a tail call: through a plain one, gcc inlines it
    // but turns its own tail calls to Context::exit into calls, and every
    // handler gets a frame.
    // A slot's first slot_lead bytes are where PUSH1 lands, on the opcode
    // after its immediate (push<1>), its stack tested. For most opcodes they
    // are PUSH1 itself, falling into the opcode's handler, which the linker
    // script places right after them: the immediate pushed, PUSH1's gas
    // charged and instr_ptr moved past it, in a3, a4 and a5, the handlers'
    // stack_top, gas_remaining and instr_ptr. For the opcodes push1_then
    // fuses with PUSH1, a jump to the pair, compiled into the end of the slot.
    #define MONAD_VM_LEAD_PUSH(REV, NAME, OP)                                  \
        static_assert(                                                         \
            compiler::opcode_table<EvmTraits<REV>>[PUSH1].min_gas == 3 &&      \
            sizeof(uint256_t) == 32 && slot_lead == 32);                       \
        asm(".pushsection .monad_vm_lead." #NAME "." #OP ",\"ax\",@progbits\n" \
            ".type monad_vm_slot_" #NAME "_" #OP "_lead, @function\n"          \
            "monad_vm_slot_" #NAME "_" #OP "_lead:\n"                          \
            "\tlbu t3, 1(a5)\n"                                                \
            "\tsd t3, 32(a3)\n"                                                \
            "\tsd zero, 40(a3)\n"                                              \
            "\tsd zero, 48(a3)\n"                                              \
            "\tsd zero, 56(a3)\n"                                              \
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
                MONAD_VM_ANALYSIS_PARAM,                                       \
                uint256_t const *const stack_bottom,                           \
                uint256_t *const stack_top,                                    \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const itbl)                                        \
        {                                                                      \
            __attribute__((musttail)) return push1_then<                       \
                0x##OP,                                                        \
                EvmTraits<REV>>(                                               \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                itbl);                                                         \
        }

    // The followers push1_then takes: ADD, SHL, SHR, SAR, MLOAD, MSTORE and
    // PUSH1. The others' MONAD_VM_PUSH1_PAIR_xx is undefined, and
    // MONAD_VM_LEAD_KIND takes the default after it.
    #define MONAD_VM_PUSH1_PAIR_01 ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_1b ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_1c ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_1d ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_51 ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_52 ~, PAIR
    #define MONAD_VM_PUSH1_PAIR_60 ~, PAIR
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
                MONAD_VM_ANALYSIS_PARAM,                                       \
                uint256_t const *const stack_bottom,                           \
                uint256_t *const stack_top,                                    \
                int64_t const gas_remaining,                                   \
                uint8_t const *const instr_ptr,                                \
                void const *const itbl)                                        \
        {                                                                      \
            constexpr InstrEval handler =                                      \
                instruction_table<EvmTraits<REV>>[0x##OP];                     \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top,                                                     \
                gas_remaining,                                                 \
                instr_ptr,                                                     \
                itbl);                                                         \
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
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t *const stack_ptr)
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
        trampoline(ctx, analysis, stack_ptr, core_loop<traits>);
    }

    EXPLICIT_TRAITS(execute);
}
