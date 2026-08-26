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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>
#include <nlohmann/json_fwd.hpp>

#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

class AccountState;
class State;

class AccessListTracer
{
public:
    using IsPrecompileFn = bool (*)(Address const &);

    using Signature = monad::Signature<
        trace::state_trace::State, trace::state_trace::RejectFrame,
        trace::state_trace::Reset>;

    AccessListTracer(
        nlohmann::json &storage, Address const &sender,
        Address const &beneficiary, std::optional<Address> const &to,
        std::span<std::optional<Address> const> authorities,
        bool dedup_storage_pages = false,
        IsPrecompileFn is_precompile = nullptr);

    template <Traits traits>
    void encode(State &state);

    void operator()(trace::state_trace::State const &);
    void operator()(trace::state_trace::RejectFrame const &);
    void operator()(trace::state_trace::Reset const &);

private:
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    template <class Key>
    using Set = ankerl::unordered_dense::set<Key>;

    void capture_accesses(Address const &, AccountState const &);
    void capture_accesses(State const &);
    void capture_rejected_frame_accesses(State const &);
    void encode(State const &);
    bool should_exclude_address(Address const &) const;

    nlohmann::json &storage_;
    Set<Address> excluded_addresses_{};
    Map<Address, Set<bytes32_t>> accesses_{};
    bool dedup_storage_pages_;
    IsPrecompileFn is_precompile_;
};

MONAD_NAMESPACE_END
