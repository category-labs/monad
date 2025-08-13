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

#include <category/vm/core/assert.h>
#include <category/vm/interpreter/instruction_table.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/traits.hpp>

#include <evmc/evmc.h>

#include <cstdint>

/**
 * Assembly trampoline into the interpreter's core loop (see entry.S). This
 * function sets up the stack to be compatible with the runtime's exit ABI, then
 * jumps to `monad_vm_interpreter_core_loop`. It is therefore important that
 * these two functions always maintain the same signature (so that arguments are
 * in the expected registers when jumping to the core loop).
 */
extern "C" void monad_vm_interpreter_trampoline(
    void *, evmc_revision, ::monad::vm::runtime::Context *,
    ::monad::vm::interpreter::Intercode const *,
    ::monad::vm::runtime::uint256_t *);

extern "C" void monad_vm_interpreter_core_loop(
    void *, evmc_revision, ::monad::vm::runtime::Context *,
    ::monad::vm::interpreter::Intercode const *,
    ::monad::vm::runtime::uint256_t *);

static_assert(
    ::monad::vm::utils::same_signature(
        monad_vm_interpreter_trampoline, monad_vm_interpreter_core_loop),
    "Interpreter core loop and trampoline signatures must be identical");

#define ASM_COMMENT(C) asm volatile("# " C);

namespace monad::vm::interpreter
{
    namespace
    {
        template <evmc_revision Rev>
#if defined(__GNUC__) && !defined(__clang__)
        __attribute__((optimize("-falign-labels=16")))
#endif
        void
        core_loop_impl(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t *stack_ptr)
        {
            auto *const stack_top = stack_ptr - 1;
            auto const *const stack_bottom = stack_top;
            auto const *const instr_ptr = analysis.code();
            auto const gas_remaining = ctx.gas_remaining;

            instruction_table<Rev>[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    }

    void execute(
        evmc_revision rev, runtime::Context &ctx, Intercode const &analysis,
        std::uint8_t *stack_ptr)
    {
        monad_vm_interpreter_trampoline(
            static_cast<void *>(&ctx.exit_stack_ptr),
            rev,
            &ctx,
            &analysis,
            reinterpret_cast<runtime::uint256_t *>(stack_ptr));
    }
}

extern "C" void monad_vm_interpreter_core_loop(
    void *, evmc_revision rev, ::monad::vm::runtime::Context *ctx,
    ::monad::vm::interpreter::Intercode const *analysis,
    ::monad::vm::runtime::uint256_t *stack_ptr)
{
    using namespace ::monad::vm::interpreter;

    switch (rev) {
    case EVMC_FRONTIER:
        return core_loop_impl<EVMC_FRONTIER>(*ctx, *analysis, stack_ptr);
    case EVMC_HOMESTEAD:
        return core_loop_impl<EVMC_HOMESTEAD>(*ctx, *analysis, stack_ptr);
    case EVMC_TANGERINE_WHISTLE:
        return core_loop_impl<EVMC_TANGERINE_WHISTLE>(
            *ctx, *analysis, stack_ptr);
    case EVMC_SPURIOUS_DRAGON:
        return core_loop_impl<EVMC_SPURIOUS_DRAGON>(*ctx, *analysis, stack_ptr);
    case EVMC_BYZANTIUM:
        return core_loop_impl<EVMC_BYZANTIUM>(*ctx, *analysis, stack_ptr);
    case EVMC_CONSTANTINOPLE:
        return core_loop_impl<EVMC_CONSTANTINOPLE>(*ctx, *analysis, stack_ptr);
    case EVMC_PETERSBURG:
        return core_loop_impl<EVMC_PETERSBURG>(*ctx, *analysis, stack_ptr);
    case EVMC_ISTANBUL:
        return core_loop_impl<EVMC_ISTANBUL>(*ctx, *analysis, stack_ptr);
    case EVMC_BERLIN:
        return core_loop_impl<EVMC_BERLIN>(*ctx, *analysis, stack_ptr);
    case EVMC_LONDON:
        return core_loop_impl<EVMC_LONDON>(*ctx, *analysis, stack_ptr);
    case EVMC_PARIS:
        return core_loop_impl<EVMC_PARIS>(*ctx, *analysis, stack_ptr);
    case EVMC_SHANGHAI:
        return core_loop_impl<EVMC_SHANGHAI>(*ctx, *analysis, stack_ptr);
    case EVMC_CANCUN:
        return core_loop_impl<EVMC_CANCUN>(*ctx, *analysis, stack_ptr);
    case EVMC_PRAGUE:
        return core_loop_impl<EVMC_PRAGUE>(*ctx, *analysis, stack_ptr);
    default:
        MONAD_VM_ASSERT(false);
    }
}
