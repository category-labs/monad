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

namespace monad::vm::interpreter
{
    namespace
    {
        template <Traits traits>
        void core_loop(
            void *, runtime::Context *ctx, Intercode const *analysis,
            uint256_t *stack_ptr, void *)
        {
            auto *const stack_top = stack_ptr - 1;
            auto const *const stack_bottom = stack_top;
            auto const *const instr_ptr = analysis->code();
            auto const gas_remaining = ctx->gas_remaining;

            if constexpr (debug_enabled) {
                trace(*analysis, gas_remaining, instr_ptr);
            }
            // The table's base is materialised once, here, and then rides in
            // an argument register for the whole tail-call chain.
#if defined(MONAD_VM_TABLE_ARG)
            auto const *const itbl = instruction_table<traits>.data();
#endif
            instruction_table<traits>[*instr_ptr](
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
        // core_loop takes stack_bottom as stack_ptr - 1, so the first slot an
        // opcode may not occupy is stack_ptr + 1023.
        ctx.stack_limit = reinterpret_cast<uint256_t *>(stack_ptr) + 1023;
#if defined(MONAD_ZKVM_ZISK)
        // Here and not as a member initialiser on Context. Context is not
        // always built by a C++ constructor -- context.S assembles it, which is
        // why the offsets above it are pinned by static_assert -- so a default
        // member initialiser is not guaranteed to have run. Set with
        // stack_limit, which the comment on that member says is the same
        // situation, and which is the only path that can reach an opcode.
        //
        // The first build that relied on the member initialiser wrote add256's
        // result through an uninitialised pointer: the run died after 19.6 M
        // steps having published zeros, and `-X` counted no add256 at all.
        ctx.add256_params.cin = 0;
        ctx.add256_params.c = ctx.add256_out;
#endif
        trampoline(
            ctx,
            analysis,
            reinterpret_cast<uint256_t *>(stack_ptr),
            core_loop<traits>);
    }

    EXPLICIT_TRAITS(execute);
}
