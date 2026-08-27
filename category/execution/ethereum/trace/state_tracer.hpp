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

#pragma once

#include <category/core/config.hpp>
#include <category/vm/evm/traits.hpp>

#include <variant>

MONAD_NAMESPACE_BEGIN

class State;

namespace trace
{
    using StateTracer = std::monostate;

    // State-tracer lifecycle hook for a failed frame. Call immediately before
    // State::pop_reject(), while rejected-frame access metadata is still
    // visible through State.
    void on_frame_reject(StateTracer &, State &);

    // Clear execution-attempt-local tracer state before speculative execution.
    void reset(StateTracer &);

    // Finalise and serialise tracer output after transaction execution, once
    // accepted-frame state has been merged into the visible State view.
    template <Traits traits>
    void run_tracer(StateTracer &tracer, State &state);
}

MONAD_NAMESPACE_END
