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

#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <nlohmann/json_fwd.hpp>

MONAD_NAMESPACE_BEGIN

class State;

namespace trace
{
    nlohmann::json state_deltas_to_json(StateDeltas const &, State &);
    void state_deltas_to_json(StateDeltas const &, State &, nlohmann::json &);
}

class StateDiffTracer
{
public:
    using Signature = monad::Signature<trace::state_trace::State>;

    explicit StateDiffTracer(nlohmann::json &storage);

    void operator()(trace::state_trace::State const &op);

private:
    StorageDeltas generate_storage_deltas(
        AccountState::StorageMap const &, AccountState::StorageMap const &);
    StateDeltas build_state_deltas(State const &state);

    nlohmann::json &storage_;
};

MONAD_NAMESPACE_END