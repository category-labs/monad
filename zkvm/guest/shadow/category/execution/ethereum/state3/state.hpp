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

// The guest's stand-in for the native state3/state.hpp. The execution layer
// is written against the concrete class monad::State, so in a guest build
// that name is the guest state: a final class deriving from zkvm::State
// with nothing of its own. The guest class keeps its own namespace so that
// the host's unit tests can link it beside the native State; this header
// is found first only by translation units compiled with
// zkvm/guest/shadow on their include path, which is every execution source
// the guest keeps and the guest driver itself.

#include <category/core/config.hpp>
#include <category/execution/ethereum/state3/state_interface.hpp>
#include <zkvm/state/state.hpp>

MONAD_NAMESPACE_BEGIN

class State final : public zkvm::State
{
public:
    using zkvm::State::State;
};

static_assert(StateInterface<State>);

MONAD_NAMESPACE_END
