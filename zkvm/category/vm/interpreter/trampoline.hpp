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

// Guest trampoline: setjmp saves the return point used by runtime::exit's
// longjmp. The jump buffer lives until the core loop exits.

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

#include <csetjmp>

namespace monad::vm::interpreter
{
    using core_loop_fn_t = void (*)(
        void *, runtime::Context *, Intercode const *, uint256_t *, void *);

    // Make the call target a compile-time constant, not an argument saved
    // across setjmp. Do not force inlining: GCC rejects it with setjmp.
    template <core_loop_fn_t core_loop_fn>
    void trampoline(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t *const stack_ptr)
    {
        std::jmp_buf jb;
        if (setjmp(jb) == 0) {
            ctx.exit_stack_ptr = &jb;
            core_loop_fn(nullptr, &ctx, &analysis, stack_ptr, nullptr);
        }
    }
}
