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

// zkVM mirror: the trampoline is implemented inline with setjmp/longjmp instead
// of via the host's hand-rolled assembly (entry.S). GCC forbids inlining
// functions that use setjmp so for now we cannot guarantee that the jmp_buf
// lives on the caller's stack frame.
//
// longjmp from monad::vm::runtime::exit lands back here and we return.

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

#include <csetjmp>

namespace monad::vm::interpreter
{
    using core_loop_fn_t = void (*)(
        void *, runtime::Context *, Intercode const *, uint256_t *, void *);

    // No [[gnu::always_inline]] here — GCC forbids inlining functions
    // that call setjmp. The optimizer may still inline opportunistically.
    inline void trampoline(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t *const stack_ptr, core_loop_fn_t core_loop_fn)
    {
        std::jmp_buf jb;
        if (setjmp(jb) == 0) {
            ctx.exit_stack_ptr = &jb;
            core_loop_fn(nullptr, &ctx, &analysis, stack_ptr, nullptr);
        }
    }
}
