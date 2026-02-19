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

#include <category/vm/runtime/types.hpp>

#ifdef MONAD_ZKVM
    #include <csetjmp>
#else
extern "C" void monad_vm_runtime_exit [[noreturn]] (void *);
#endif

extern "C" void monad_vm_runtime_context_out_of_gas_exit
    [[noreturn]] (monad::vm::runtime::Context *ctx)
{
    ctx->result.status = monad::vm::runtime::StatusCode::OutOfGas;
#ifdef MONAD_ZKVM
    std::longjmp(*ctx->exit_stack_ptr, 1);
#else
    monad_vm_runtime_exit(ctx->exit_stack_ptr);
#endif
}

namespace monad::vm::runtime
{
    void Context::stack_unwind [[noreturn]] () noexcept
    {
        is_stack_unwinding_active = true;
        result.status = StatusCode::Error;
#ifdef MONAD_ZKVM
        std::longjmp(*exit_stack_ptr, 1);
#else
        monad_vm_runtime_exit(exit_stack_ptr);
#endif
    }

    void Context::exit [[noreturn]] (StatusCode code) noexcept
    {
        result.status = code;
#ifdef MONAD_ZKVM
        std::longjmp(*exit_stack_ptr, 1);
#else
        monad_vm_runtime_exit(exit_stack_ptr);
#endif
    }
}
