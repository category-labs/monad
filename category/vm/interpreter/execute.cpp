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
    #define MONAD_VM_SLOT(REV, NAME, OP)                                       \
        extern "C" [[gnu::section(".monad_vm_slot." #NAME "." #OP)]] void      \
        monad_vm_slot_##NAME##_##OP(                                           \
            runtime::Context &ctx,                                             \
            Intercode const &analysis,                                         \
            uint256_t const *const stack_bottom,                               \
            uint256_t *const stack_top,                                        \
            int64_t const gas_remaining,                                       \
            uint8_t const *const instr_ptr,                                    \
            void const *const itbl)                                            \
        {                                                                      \
            constexpr InstrEval handler =                                      \
                instruction_table<EvmTraits<REV>>[0x##OP];                     \
            __attribute__((musttail)) return handler(                          \
                ctx,                                                           \
                analysis,                                                      \
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
                itbl =
                    monad_vm_slots + ((MONAD_ETH_AMSTERDAM - traits::evm_rev())
                                      << 8 << slot_shift);
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
                *analysis,
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
#endif
        trampoline(
            ctx,
            analysis,
            reinterpret_cast<uint256_t *>(stack_ptr),
            core_loop<traits>);
    }

    EXPLICIT_TRAITS(execute);
}
