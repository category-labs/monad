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
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>
#include <immer/map.hpp>
#include <nlohmann/json.hpp>

#include <span>
#include <variant>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

namespace trace
{
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    template <class Key>
    using Set = ankerl::unordered_dense::set<Key>;

    struct PrestateTracer
    {
        explicit PrestateTracer(
            nlohmann::json &storage, Address const &beneficiary)
            : storage_(storage)
            , beneficiary_(beneficiary)
        {
        }

        void encode(Map<Address, OriginalAccountState> const &, State &);

    private:
        bool retain_beneficiary(State const &state) const;
        static nlohmann::json
        account_state_to_json(OriginalAccountState const &, State &);
        static void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &);
        static nlohmann::json state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &);
        friend void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &);
        friend nlohmann::json state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &);
        static nlohmann::json
        reserve_balance_state_to_json(OriginalAccountState const &, State &);
        nlohmann::json &storage_;
        Address const &beneficiary_;
    };

    struct StateDiffTracer
    {
        explicit StateDiffTracer(nlohmann::json &storage)
            : storage_(storage)
        {
        }

        StateDeltas trace(State const &state);
        void encode(StateDeltas const &, State &);

    private:
        nlohmann::json &storage_;
    };

    struct AccessListTracer
    {
        AccessListTracer(
            nlohmann::json &storage, Address const &sender,
            Address const &beneficiary, std::optional<Address> const &to,
            std::span<std::optional<Address> const> const authorities);

        template <Traits traits>
        void encode(State &);

    private:
        nlohmann::json &storage_;
        Set<Address> excluded_addresses_ = {RESERVE_BALANCE_CA};

        template <Traits traits>
        bool should_exclude_address(Address const &) const;
    };

    using StateTracer = std::variant<
        std::monostate, PrestateTracer, StateDiffTracer, AccessListTracer>;

    template <Traits traits>
    void run_tracer(StateTracer &tracer, State &state);

    nlohmann::json state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &);
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);
    nlohmann::json state_deltas_to_json(StateDeltas const &, State &);
    void state_deltas_to_json(StateDeltas const &, State &, nlohmann::json &);
}

MONAD_NAMESPACE_END
