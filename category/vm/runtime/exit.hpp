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

// Host unwind primitive. On the host build the actual implementation is
// the hand-rolled assembly in exit.S; the inline `exit` wrapper here
// gives call sites a single typed entry point so the zkVM mirror can
// supply an inline setjmp/longjmp variant without any extern call.

#pragma once

namespace monad::vm::runtime
{
    using exit_stack_ptr_t = void *;
}

extern "C" void monad_vm_runtime_exit
    [[noreturn]] (monad::vm::runtime::exit_stack_ptr_t);

namespace monad::vm::runtime
{
    [[gnu::always_inline, noreturn]]
    inline void exit(exit_stack_ptr_t p)
    {
        monad_vm_runtime_exit(p);
    }
}
