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

#pragma once

#include <category/core/throw.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/engine_timer.hpp>
#include <category/vm/runtime/types.hpp>

#include <exception>
#include <utility>

namespace monad::vm::runtime
{
    /// Calls host function `f` from VM code. The time is charged to the host,
    /// and an exception unwinds the frame instead of VM code; `VM::execute`
    /// rethrows it once the frame has returned.
    template <auto f, typename... Args>
    [[gnu::always_inline]]
    inline decltype(auto) call_host(Context *const ctx, Args &&...args)
    {
        MONAD_TRY
        {
            EngineTimer::Scope const timer{
                ctx->engine_timer, EngineTimer::Host};
            return (ctx->host->*f)(std::forward<Args>(args)...);
        }
        MONAD_CATCH(...)
        {
            ctx->host_exception = std::current_exception();
        }
        ctx->stack_unwind();
    }
}
