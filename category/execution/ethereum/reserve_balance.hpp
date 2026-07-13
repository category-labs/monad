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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct BlockMetrics;
class State;
struct Transaction;

template <Traits traits>
bool revert_transaction(
    Address const &sender, Transaction const &,
    uint256_t const &base_fee_per_gas, uint64_t i, State &,
    trace::StateTracer &state_tracer, ChainContext<traits> const &);

template <Traits traits>
bool revert_transaction_cached(State &);

template <Traits traits>
    requires is_monad_trait_v<traits>
void init_reserve_balance_context(
    State &state, Address const &sender, Transaction const &tx,
    std::optional<uint256_t> const &base_fee_per_gas, uint64_t i,
    trace::StateTracer &state_tracer, ChainContext<traits> const &ctx);

/// Fold this transaction's reserve-balance dip outcome into the block
/// metrics: whether the sender was eligible to dip into its reserve, and —
/// for successful transactions only — whether the sender's allowed-dip
/// exemption is what saved the transaction from a reserve-balance revert.
/// Failed transactions never count as dips: they would have failed with or
/// without the exemption. Returns whether the transaction was counted as a
/// dip. No-op returning false for EVM traits and Monad revisions before
/// MONAD_FOUR, where the reserve is not enforced.
template <Traits traits>
bool record_reserve_dip_metrics(
    State const &state, bool tx_succeeded, BlockMetrics &metrics);

MONAD_NAMESPACE_END
