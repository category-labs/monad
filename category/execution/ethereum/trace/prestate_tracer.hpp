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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <ankerl/unordered_dense.h>
#include <nlohmann/json_fwd.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

class OriginalAccountState;
class State;

namespace trace
{
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    nlohmann::json state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &);
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);
}

class PrestateTracer
{
public:
    using Signature = monad::Signature<trace::state_trace::State>;

    explicit PrestateTracer(
        nlohmann::json &storage, Address const &beneficiary);

    void operator()(trace::state_trace::State const &op);

private:
    bool retain_beneficiary(State const &) const;

    static nlohmann::json
    account_state_to_json(OriginalAccountState const &, State &);
    static void state_to_json(
        trace::Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);
    friend nlohmann::json trace::state_to_json(
        trace::Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &);
    friend void trace::state_to_json(
        trace::Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);

    nlohmann::json &storage_;
    Address const &beneficiary_;
};

MONAD_NAMESPACE_END
