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
bool dipped_into_reserve(State &state)
{
    MONAD_ASSERT(state.reserve_balance_tracking_enabled());
    return state.reserve_balance_has_violation();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

ReserveBalance::ReserveBalance(State *state)
    : state_{state}
{
}

bool ReserveBalance::tracking_enabled() const
{
    return tracking_enabled_;
}

bool ReserveBalance::has_violation() const
{
    return !failed_.empty();
}

bool ReserveBalance::failed_contains(Address const &address) const
{
    return failed_.contains(address);
}

bool ReserveBalance::subject_account(Address const &address)
{
    OriginalAccountState &orig_state = state_->original_account_state(address);
    bytes32_t const effective_code_hash = use_recent_code_hash_
                                              ? state_->get_code_hash(address)
                                              : orig_state.get_code_hash();
    if (effective_code_hash == NULL_HASH) {
        return true;
    }
    return state_->is_delegated(effective_code_hash);
}

uint256_t ReserveBalance::pretx_reserve(Address const &address)
{
    MONAD_ASSERT(get_max_reserve_);
    uint256_t const max_reserve = get_max_reserve_(address);
    return std::min(max_reserve, state_->get_original_balance(address));
}

void ReserveBalance::update_violation_status(
    Address const &address, AccountState &account_state)
{
    if (!tracking_enabled_) {
        return;
    }

    if (!account_state.rb_violation_threshold_cached()) {
        if (!subject_account(address)) {
            account_state.set_rb_violation_threshold(uint256_t{0});
            failed_.erase(address);
            account_state.set_rb_failed(false);
            return;
        }

        uint256_t reserve = pretx_reserve(address);
        if (address == sender_) {
            if (sender_can_dip_) {
                account_state.set_rb_violation_threshold(uint256_t{0});
                failed_.erase(address);
                account_state.set_rb_failed(false);
                return;
            }
            MONAD_ASSERT_THROW(
                sender_gas_fees_ <= reserve,
                "gas fee greater than reserve for non-dipping transaction");
            reserve = reserve - sender_gas_fees_;
        }
        account_state.set_rb_violation_threshold(reserve);
    }

    uint256_t const violation_threshold =
        account_state.rb_violation_threshold();
    if (violation_threshold == 0) {
        failed_.erase(address);
        account_state.set_rb_failed(false);
        return;
    }

    if (state_->get_balance(address) < violation_threshold) {
        failed_.insert(address);
        account_state.set_rb_failed(true);
    }
    else {
        failed_.erase(address);
        account_state.set_rb_failed(false);
    }
}

void ReserveBalance::on_credit(
    Address const &address, AccountState &account_state)
{
    if (!tracking_enabled_) {
        return;
    }
    if (failed_.contains(address)) {
        update_violation_status(address, account_state);
    }
}

void ReserveBalance::on_debit(
    Address const &address, AccountState &account_state)
{
    update_violation_status(address, account_state);
}

void ReserveBalance::on_pop_reject(FailedSet const &accounts)
{
    if (!tracking_enabled_) {
        return;
    }
    for (auto const &dirty_address : accounts) {
        if (state_->rb_failed_flag(dirty_address)) {
            failed_.insert(dirty_address);
        }
        else {
            failed_.erase(dirty_address);
        }
    }
}

void ReserveBalance::on_set_code(
    Address const &address, AccountState &account_state,
    byte_string_view const code)
{
    if (!tracking_enabled_) {
        return;
    }
    if (!use_recent_code_hash_) {
        return;
    }
    if (!vm::evm::is_delegated({code.data(), code.size()})) {
        account_state.set_rb_violation_threshold(uint256_t{0});
        account_state.set_rb_failed(false);
        failed_.erase(address);
        return;
    }
    account_state.clear_rb_violation_threshold();
    update_violation_status(address, account_state);
}

template <Traits traits>
    requires is_monad_trait_v<traits>
void ReserveBalance::init_from_tx(
    Address const &sender, Transaction const &tx,
    std::optional<uint256_t> const &base_fee_per_gas, uint64_t i,
    ChainContext<traits> const &ctx)
{
    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());
    use_recent_code_hash_ = traits::monad_rev() >= MONAD_EIGHT;
    bytes32_t const sender_code_hash =
        use_recent_code_hash_
            ? state_->get_code_hash(sender)
            : state_->original_account_state(sender).get_code_hash();
    bool const sender_can_dip = can_sender_dip_into_reserve<traits>(
        sender, i, state_->is_delegated(sender_code_hash), ctx);
    tracking_enabled_ = true;
    sender_ = sender;
    sender_gas_fees_ = uint256_t{tx.gas_limit} *
                       gas_price<traits>(tx, base_fee_per_gas.value_or(0));
    sender_can_dip_ = sender_can_dip;
    get_max_reserve_ = [](Address const &addr) {
        return get_max_reserve<traits>(addr);
    };
    failed_.clear();
}

EXPLICIT_MONAD_TRAITS_MEMBER(ReserveBalance::init_from_tx);

template <Traits traits>
bool revert_transaction(State &state)
{
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        return dipped_into_reserve<traits>(state);
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
