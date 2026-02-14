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
#include <category/core/monad_exception.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <algorithm>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

static ankerl::unordered_dense::segmented_set<monad::Address> const
    empty_senders_and_authorities{};
static std::vector<monad::Address> const empty_senders{monad::Address{0}};
static std::vector<std::vector<std::optional<monad::Address>>> const
    empty_authorities{{}};

template <Traits traits>
bool dipped_into_reserve(
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i,
    ChainContext<traits> const &ctx, State &state)
{
    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());

    uint256_t const gas_fees =
        uint256_t{tx.gas_limit} * gas_price<traits>(tx, base_fee_per_gas);
    auto const &orig = state.original();
    for (auto const &[addr, cur_account] : state.current()) {
        MONAD_ASSERT(orig.contains(addr));
        bytes32_t const orig_code_hash = orig.at(addr).get_code_hash();
        bytes32_t const effective_code_hash =
            (traits::monad_rev() >= MONAD_EIGHT)
                ? cur_account.recent().get_code_hash()
                : orig_code_hash;
        bool effective_is_delegated = false;

        // Skip if not EOA
        if (effective_code_hash != NULL_HASH) {
            vm::SharedIntercode const intercode =
                state.read_code(effective_code_hash)->intercode();
            effective_is_delegated = monad::vm::evm::is_delegated(
                {intercode->code(), intercode->size()});
            if (!effective_is_delegated) {
                continue;
            }
        }

        // Check if dipped into reserve
        std::optional<uint256_t> const violation_threshold =
            [&] -> std::optional<uint256_t> {
            ReserveBalanceView reserve_view{state};
            uint256_t const delayed_urb = reserve_view.get_delayed_urb(addr);
            uint256_t const orig_balance = state.get_original_balance(addr);
            uint256_t const reserve = std::min(delayed_urb, orig_balance);
            if (addr == sender) {
                if (gas_fees > reserve) { // must be dipping
                    return std::nullopt;
                }
                return reserve - gas_fees;
            }
            return reserve;
        }();
        uint256_t const curr_balance = state.get_balance(addr);
        if (!violation_threshold.has_value() ||
            curr_balance < violation_threshold.value()) {
            if (addr == sender) {
                if (!can_sender_dip_into_reserve(
                        sender, i, effective_is_delegated, ctx)) {
                    // Safety: this assertion is recoverable because it can be
                    // triggered via RPC parameter setting.
                    MONAD_ASSERT_THROW(
                        violation_threshold.has_value(),
                        "gas fee greater than reserve for non-dipping "
                        "transaction");
                    return true;
                }
                // Skip if allowed to dip into reserve
            }
            else {
                // Safety: this assertion should not be a recoverable one, as it
                // indicates a logic error in the surrounding code: the
                // violation threshold can only be nullopt when addr == sender,
                // which is not the case in this branch.
                MONAD_ASSERT(violation_threshold.has_value());
                return true;
            }
        }
    }
    return false;
}

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

MONAD_NAMESPACE_END
