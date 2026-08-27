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

#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_NAMESPACE_BEGIN

namespace trace
{
    void on_frame_reject(StateTracer &tracer, State &state)
    {
        static_cast<void>(tracer);
        static_cast<void>(state);
    }

    void reset(StateTracer &tracer)
    {
        static_cast<void>(tracer);
    }

    template <Traits traits>
    void run_tracer(StateTracer &tracer, State &state)
    {
        static_cast<void>(tracer);
        static_cast<void>(state);
    }

    EXPLICIT_TRAITS(run_tracer);
}

MONAD_NAMESPACE_END