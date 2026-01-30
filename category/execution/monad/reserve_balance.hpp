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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <ankerl/unordered_dense.h>

#include <evmc/evmc.h>

#include <cstdint>
#include <functional>
#include <functional>

MONAD_NAMESPACE_BEGIN

class AccountState;
class OriginalAccountState;
class AccountState;
class OriginalAccountState;
class State;
struct Transaction;

class ReserveBalance
{
    using FailedSet = ankerl::unordered_dense::segmented_set<Address>;

    State *state_;
    bool tracking_enabled_{false};
    bool use_recent_code_hash_{false};
    Address sender_{};
    uint256_t sender_gas_fees_{0};
    bool sender_can_dip_{false};
    FailedSet failed_{};
    std::function<uint256_t(Address const &)> get_max_reserve_{};

    bool subject_account(Address const &);
    uint256_t reserve_cap(Address const &, OriginalAccountState &);

public:
    explicit ReserveBalance(State *state);

    void set_context(
        Address const &sender, uint256_t const &gas_fees,
        bool use_recent_code_hash, bool sender_can_dip,
        std::function<uint256_t(Address const &)> get_max_reserve);

    bool tracking_enabled() const;

    bool has_violation() const;

    bool failed_contains(Address const &address) const;

    void update_violation(Address const &, AccountState *account_state);

    void on_pop_reject(FailedSet const &accounts);

    void on_code_change(Address const &address, AccountState &account_state);

    void prime_original_state(
        OriginalAccountState &orig_state, bytes32_t const &code_hash);

    template <Traits traits>
        requires is_monad_trait_v<traits>
    void init_from_tx(
        Address const &sender, Transaction const &tx,
        BlockHeader const &header, uint64_t i, ChainContext<traits> const &ctx)
    {
        bytes32_t const sender_code_hash =
            (traits::monad_rev() >= MONAD_EIGHT)
                ? state_->get_code_hash(sender)
                : state_->original_account_state(sender).get_code_hash();
        bool const sender_is_delegated = state_->is_delegated(sender_code_hash);

        bool const sender_can_dip = can_sender_dip_into_reserve<traits>(
            sender, i, sender_is_delegated, ctx);
        set_context(
            sender,
            uint256_t{tx.gas_limit} *
                gas_price<traits>(tx, header.base_fee_per_gas.value_or(0)),
            traits::monad_rev() >= MONAD_EIGHT,
            sender_can_dip,
            [](Address const &addr) {
                return get_max_reserve<traits>(addr);
            });
    }
};

class ReserveBalance
{
    using FailedSet = ankerl::unordered_dense::segmented_set<Address>;

    State *state_;
    bool tracking_enabled_{false};
    bool use_recent_code_hash_{false};
    Address sender_{};
    uint256_t sender_gas_fees_{0};
    bool sender_can_dip_{false};
    FailedSet failed_{};
    std::function<uint256_t(Address const &)> get_max_reserve_{};

    bool subject_account(Address const &);
    uint256_t reserve_cap(Address const &, OriginalAccountState &);

public:
    explicit ReserveBalance(State *state);

    void set_context(
        Address const &sender, uint256_t const &gas_fees,
        bool use_recent_code_hash, bool sender_can_dip,
        std::function<uint256_t(Address const &)> get_max_reserve);

    bool tracking_enabled() const;

    bool has_violation() const;

    bool failed_contains(Address const &address) const;

    void update_violation(Address const &, AccountState *account_state);

    void on_pop_reject(FailedSet const &accounts);

    void on_code_change(Address const &address, AccountState &account_state);
};

template <Traits traits>
    requires is_monad_trait_v<traits>
bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t i, bool sender_is_delegated,
    ChainContext<traits> const &);

template <Traits traits>
uint256_t get_max_reserve(Address const &);

MONAD_NAMESPACE_END
