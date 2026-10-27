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

#include <category/execution/ethereum/state3/state.hpp>

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

OriginalAccountState &State::original_account_state(Address const &address)
{
    auto it = original_.find(address);
    if (it == original_.end()) {
        // block state
        auto const account = block_state_.read_account(address);
        it = original_.try_emplace(address, account).first;
    }
    return it->second;
}

State::State(
    BlockState &block_state, Incarnation const incarnation,
    bool const relaxed_validation)
    : block_state_{block_state}
    , incarnation_{incarnation}
    , relaxed_validation_{relaxed_validation}
    , rb_{this}
{
}

uint256_t State::get_balance(Address const &address)
{
    auto const &account = recent_account(address);
    original_account_state(address).set_validate_exact_balance();
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().balance;
    }
    return 0;
}

uint256_t State::get_original_balance(Address const &address)
{
    return original_account_state(address).get_balance_pessimistic();
}

bool State::record_balance_constraint_for_debit(
    Address const &address, uint256_t const &debit)
{
    auto const &account = recent_account(address);
    uint256_t const balance = account.has_value() ? account->balance : 0;

    auto &original_state = original_account_state(address);
    // RELAXED MERGE
    // if current balance  >= `debit`, then:
    // 1. compute the amount that current balance exceeds `debit`
    // 2. require that the original balance at merge time is at least the
    // original balance used during this execution less said excess
    if (balance >= debit) {
        uint256_t const diff = balance - debit;
        auto const &original = original_state.account();
        uint256_t const original_balance =
            original.has_value() ? original->balance : 0;
        if (original_balance > diff) { // avoid underflow when <= diff
            uint256_t const min_balance =
                original_balance -
                diff; // original balance - current balance + debit
            original_state.set_min_balance(min_balance);
        }
        return true;
    }

    // otherwise require that original balance at merge time matches
    // original balance used during this execution exactly
    original_state.set_validate_exact_balance();
    return false;
}

void State::set_original_nonce(Address const &address, uint64_t const nonce)
{
    auto &account_state = original_account_state(address);
    auto &account = account_state.account();
    if (!account.has_value()) {
        account = Account{};
    }
    account->nonce = nonce;
}

MONAD_NAMESPACE_END
