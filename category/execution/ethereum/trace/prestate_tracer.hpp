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
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>

#include <ankerl/unordered_dense.h>

#include <nlohmann/json.hpp>

#include <variant>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

namespace trace
{

    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    struct PrestateTracer
    {
        PrestateTracer(nlohmann::json &storage)
            : storage_(storage)
        {
        }

        void encode(Map<Address, OriginalAccountState> const &, State &);

    private:
        nlohmann::json &storage_;
    };

    struct StateDiffTracer
    {
        StateDiffTracer(nlohmann::json &storage)
            : storage_(storage)
        {
        }

        StateDeltas trace(State const &state);
        void encode(StateDeltas const &, State &);

    private:
        StorageDeltas generate_storage_deltas(
            Map<bytes32_t, bytes32_t> const &,
            Map<bytes32_t, bytes32_t> const &);
        nlohmann::json &storage_;
    };

    using StateTracer =
        std::variant<std::monostate, PrestateTracer, StateDiffTracer>;
    void run_tracer(StateTracer const &tracer, State &state);

    nlohmann::json
    state_to_json(Map<Address, OriginalAccountState> const &, State &);
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &, nlohmann::json &);
    nlohmann::json state_deltas_to_json(StateDeltas const &, State &);
    void state_deltas_to_json(StateDeltas const &, State &, nlohmann::json &);
}

MONAD_NAMESPACE_END
