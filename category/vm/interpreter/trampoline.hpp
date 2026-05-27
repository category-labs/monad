// Copyright (C) 2025-26 Category Labs, Inc.
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

// Host trampoline: assembly entry-point (entry.S) sets up the exit-resume
// frame and jumps to the supplied core_loop instantiation. The inline
// wrapper below gives the call site a single typed entry point so the
// zkVM mirror can substitute an inline setjmp-based variant.

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/utils/traits.hpp>

// Implemented in entry.S.
extern "C" void monad_vm_interpreter_trampoline(
    void *, ::monad::vm::runtime::Context *,
    ::monad::vm::interpreter::Intercode const *, monad::uint256_t *, void *);

namespace monad::vm::interpreter
{
    using core_loop_fn_t = void (*)(
        void *, runtime::Context *, Intercode const *, uint256_t *, void *);

    static_assert(
        utils::same_signature(
            &monad_vm_interpreter_trampoline,
            static_cast<core_loop_fn_t>(nullptr)),
        "Interpreter core loop and trampoline signatures must be "
        "identical");

    [[gnu::always_inline]]
    inline void trampoline(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t *const stack_ptr, core_loop_fn_t core_loop_fn)
    {
        monad_vm_interpreter_trampoline(
            static_cast<void *>(&ctx.exit_stack_ptr),
            &ctx,
            &analysis,
            stack_ptr,
            reinterpret_cast<void *>(core_loop_fn));
    }
}
