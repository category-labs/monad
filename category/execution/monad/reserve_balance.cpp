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
    Address const &, Transaction const &,
    uint256_t const &, uint64_t const i,
    ChainContext<traits> const &ctx, State &state)
{
    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());

    MONAD_ASSERT(state.reserve_balance_tracking_enabled());
    return state.reserve_balance_has_violation();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

ReserveBalance::ReserveBalance(State *state)
    : state_{state}
{
}

void ReserveBalance::set_context(
    Address const &sender, uint256_t const &gas_fees,
    bool const use_recent_code_hash, bool const sender_can_dip,
    std::function<uint256_t(Address const &)> get_max_reserve)
{
    tracking_enabled_ = true;
    use_recent_code_hash_ = use_recent_code_hash;
    sender_ = sender;
    sender_gas_fees_ = gas_fees;
    sender_can_dip_ = sender_can_dip;
    get_max_reserve_ = std::move(get_max_reserve);
    failed_.clear();
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
    bytes32_t const effective_code_hash =
        use_recent_code_hash_ ? state_->get_code_hash(address)
                              : orig_state.get_code_hash();
    if (effective_code_hash == NULL_HASH) {
        return true;
    }
    return state_->is_delegated(effective_code_hash);
}

uint256_t ReserveBalance::reserve_cap(
    Address const &address, OriginalAccountState &orig_state)
{
    if (!orig_state.rb_reserve_cap_cached()) {
        MONAD_ASSERT(get_max_reserve_);
        uint256_t const max_reserve = get_max_reserve_(address);
        uint256_t const reserve =
            state_->check_min_original_balance(address, max_reserve)
                ? max_reserve
                : state_->get_original_balance(address);
        orig_state.set_rb_reserve_cap(reserve);
    }
    return orig_state.rb_reserve_cap();
}

void ReserveBalance::update_violation(
    Address const &address, AccountState *account_state)
{
    if (!tracking_enabled_) {
        return;
    }

    AccountState &acct_state = account_state
                                   ? *account_state
                                   : state_->rb_account_state_or_original(
                                         address);
    OriginalAccountState &orig_state = state_->original_account_state(address);

    if (!acct_state.rb_effective_reserve_cached()) {
        if (!subject_account(address)) {
            acct_state.set_rb_effective_reserve(uint256_t{0});
            failed_.erase(address);
            return;
        }

        uint256_t const reserve = reserve_cap(address, orig_state);
        uint256_t effective_reserve = reserve;
        if (address == sender_) {
            if (sender_can_dip_) {
                acct_state.set_rb_effective_reserve(uint256_t{0});
                failed_.erase(address);
                return;
            }
            MONAD_ASSERT_THROW(
                sender_gas_fees_ <= reserve,
                "gas fee greater than reserve for non-dipping transaction");
            effective_reserve = reserve - sender_gas_fees_;
        }
        acct_state.set_rb_effective_reserve(effective_reserve);
    }

    uint256_t const effective_reserve = acct_state.rb_effective_reserve();
    if (effective_reserve == 0) {
        failed_.erase(address);
        return;
    }

    if (!state_->check_min_balance(address, effective_reserve)) {
        failed_.insert(address);
    }
    else {
        failed_.erase(address);
    }
}

void ReserveBalance::on_pop_reject(FailedSet const &accounts)
{
    if (!tracking_enabled_) {
        return;
    }
    for (auto const &dirty_address : accounts) {
        update_violation(dirty_address, nullptr);
    }
}

void ReserveBalance::on_code_change(
    Address const &address, AccountState &account_state)
{
    if (!tracking_enabled_) {
        return;
    }
    account_state.set_rb_effective_reserve(uint256_t{0});
    failed_.erase(address);
}

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
