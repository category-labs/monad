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

// zkVM mirror: the unwind path is implemented inline with setjmp/longjmp
// rather than via the host's hand-rolled asm trampoline (see exit.S).

#pragma once

#include <csetjmp>

namespace monad::vm::runtime
{
    using exit_stack_ptr_t = std::jmp_buf *;

    [[gnu::always_inline, noreturn]]
    inline void exit(exit_stack_ptr_t p)
    {
        std::longjmp(*p, 1);
    }
}
