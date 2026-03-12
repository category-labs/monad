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

#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

static ankerl::unordered_dense::segmented_set<monad::Address> const
    empty_senders_and_authorities{};
static std::vector<monad::Address> const empty_senders{monad::Address{0}};
static std::vector<std::vector<std::optional<monad::Address>>> const
    empty_authorities{{}};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision(
    uint64_t /*block_number*/, uint64_t const timestamp) const
{
    auto const monad_revision = get_monad_revision(timestamp);

    if (MONAD_LIKELY(monad_revision >= MONAD_FOUR)) {
        return EVMC_PRAGUE;
    }

    return EVMC_CANCUN;
}

template <Traits traits>
Result<void> monad_validate_transaction(
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities)
{

    auto res = ::monad::validate_transaction<traits>(tx, sender, state);
    if constexpr (MONAD_LIKELY(traits::monad_rev() >= MONAD_FOUR)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }
        uint256_t const balance = state.get_balance(sender);
        uint256_t const gas_fee =
            uint256_t{tx.gas_limit} * gas_price<traits>(tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(balance < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
        }

        if (MONAD_UNLIKELY(std::ranges::contains(authorities, SYSTEM_SENDER))) {
            return MonadTransactionError::SystemTransactionSenderIsAuthority;
        }
    }
    else if constexpr (traits::monad_rev() >= MONAD_ZERO) {
        return res;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
    return success();
}

EXPLICIT_MONAD_TRAITS(monad_validate_transaction);

Result<void> MonadChain::validate_transaction(
    [[maybe_unused]] uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> const authorities) const
{
    monad_revision const rev = get_monad_revision(timestamp);
    SWITCH_MONAD_TRAITS(
        monad_validate_transaction,
        tx,
        sender,
        state,
        base_fee_per_gas,
        authorities);
    MONAD_ASSERT(false);
}

template <typename T>
    requires is_monad_trait_v<T>
ChainContext<T> ChainContext<T>::debug_empty()
{
    return ChainContext<T>{
        .grandparent_senders_and_authorities = empty_senders_and_authorities,
        .parent_senders_and_authorities = empty_senders_and_authorities,
        .senders_and_authorities = empty_senders_and_authorities,
        .senders = empty_senders,
        .authorities = empty_authorities};
}

EXPLICIT_MONAD_TRAITS_STRUCT(ChainContext);

ankerl::unordered_dense::segmented_set<Address> combine_senders_and_authorities(
    std::span<Address const> const senders,
    std::span<std::vector<std::optional<Address>> const> const authorities)
{
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;

    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }

    for (auto const &authorities_inner : authorities) {
        for (std::optional<Address> const &authority : authorities_inner) {
            if (authority) {
                senders_and_authorities.insert(*authority);
            }
        }
    }

    return senders_and_authorities;
}

MONAD_NAMESPACE_END
