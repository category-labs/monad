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

#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/debug.hpp>
#include <category/vm/interpreter/instruction_table.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/traits.hpp>

#include <cstdint>

/**
 * Assembly trampoline into the interpreter's core loop (see entry.S). This
 * function sets up the stack to be compatible with the runtime's exit ABI, then
 * jumps to `core_loop<traits>`. It is therefore important that these two
 * functions always maintain the same signature (so that arguments are in the
 * expected registers when jumping to the core loop).
 */
extern "C" void monad_vm_interpreter_trampoline(
    void *, ::monad::vm::runtime::Context *,
    ::monad::vm::interpreter::Intercode const *,
    ::monad::vm::runtime::uint256_t *, void *);

namespace monad::vm::interpreter
{
    namespace
    {
        template <Traits traits>
        void core_loop(
            void *, runtime::Context *ctx, Intercode const *analysis,
            runtime::uint256_t *stack_ptr, void *)
        {
            static_assert(
                utils::same_signature(
                    monad_vm_interpreter_trampoline, core_loop<traits>),
                "Interpreter core loop and trampoline signatures must be "
                "identical");

            auto *const stack_top = stack_ptr - 1;
            auto const *const stack_bottom = stack_top;
            auto const *const instr_ptr = analysis->code();
            auto const gas_remaining = ctx->gas_remaining;

            if constexpr (debug_enabled) {
                trace(*analysis, gas_remaining, instr_ptr);
            }
            instruction_table<traits>[*instr_ptr](
                *ctx,
                *analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    }

    template <Traits traits>
    void execute(
        runtime::Context &ctx, Intercode const &analysis,
        std::uint8_t *stack_ptr)
    {
        monad_vm_interpreter_trampoline(
            static_cast<void *>(&ctx.exit_stack_ptr),
            &ctx,
            &analysis,
            reinterpret_cast<runtime::uint256_t *>(stack_ptr),
            reinterpret_cast<void *>(core_loop<traits>));
    }

    EXPLICIT_TRAITS(execute);
}
