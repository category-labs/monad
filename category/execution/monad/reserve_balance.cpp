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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <intx/intx.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <ranges>

unsigned monad_default_max_reserve_balance_mon(enum monad_revision)
{
    return 10;
}

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits>
bool dipped_into_reserve(
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i,
    ChainContext<traits> const &ctx, State &state)
{
    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());

    (void)tx;
    (void)base_fee_per_gas;
    (void)ctx;

    MONAD_ASSERT(state.reserve_balance_tracking_enabled());
    return state.reserve_balance_failed_other_than(sender) ||
           state.reserve_balance_failed_for(sender);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
bool revert_transaction(
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i, State &state,
    ChainContext<traits> const &ctx)
{
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        return dipped_into_reserve<traits>(
            sender, tx, base_fee_per_gas, i, ctx, state);
    }
    else if constexpr (traits::monad_rev() >= MONAD_ZERO) {
        return false;
    }
}

EXPLICIT_MONAD_TRAITS(revert_transaction);

template <Traits traits>
    requires is_monad_trait_v<traits>
bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t const i, bool const sender_is_delegated,
    ChainContext<traits> const &ctx)
{
    if (sender_is_delegated) { // delegated accounts cannot dip
        return false;
    }

    // check pending blocks
    if (ctx.grandparent_senders_and_authorities.contains(sender) ||
        ctx.parent_senders_and_authorities.contains(sender)) {
        return false;
    }

    // check current block
    if (ctx.senders_and_authorities.contains(sender)) {
        for (size_t j = 0; j <= i; ++j) {
            if (j < i && sender == ctx.senders.at(j)) {
                return false;
            }
            if (std::ranges::contains(ctx.authorities.at(j), sender)) {
                return false;
            }
        }
    }

    return true; // Allow dipping into reserve if no restrictions found
}

EXPLICIT_MONAD_TRAITS(can_sender_dip_into_reserve);

template <Traits traits>
uint256_t get_max_reserve(Address const &)
{
    // TODO: implement precompile (support reading from orig)
    constexpr uint256_t WEI_PER_MON{1000000000000000000};
    return uint256_t{
               monad_default_max_reserve_balance_mon(traits::monad_rev())} *
           WEI_PER_MON;
}

EXPLICIT_MONAD_TRAITS(get_max_reserve);

MONAD_NAMESPACE_END
