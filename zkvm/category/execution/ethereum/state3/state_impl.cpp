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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/get_storage.hpp> // IWYU pragma: keep
#include <category/execution/ethereum/types/incarnation.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

OriginalAccountState &State::original_account_state(Address const &address)
{
    auto it = original_.find(address);
    if (it == original_.end()) {
        bool resolved;
        it = original_
                 .try_emplace(
                     address, block_state_.read_account(address, resolved))
                 .first;
        if (MONAD_UNLIKELY(!resolved)) {
            it->second.mark_unresolved();
        }
    }
    return it->second;
}

std::optional<bytes32_t>
State::try_get_storage(Address const &address, bytes32_t const &key)
{
    auto const &account_state = recent_account_state(address);
    if (MONAD_UNLIKELY(
            !account_state.is_resolved() ||
            !account_state.account().has_value())) {
        return std::nullopt;
    }
    return get_storage_impl(
        address, key, [&](auto &storage, Incarnation const incarnation) {
            auto const value =
                block_state_.try_read_storage(address, incarnation, key);
            if (MONAD_LIKELY(value)) {
                storage = storage.insert({key, *value});
            }
            return value;
        });
}

State::State(
    BlockState &block_state, Incarnation const incarnation,
    bool const /*relaxed_validation*/)
    : block_state_{block_state}
    , incarnation_{incarnation}
    , rb_{this}
{
}

uint256_t State::get_balance(Address const &address)
{
    auto const &account = recent_account(address);
    if (MONAD_LIKELY(account.has_value())) {
        return account.value().balance;
    }
    return 0;
}

uint256_t State::get_original_balance(Address const &address)
{
    auto const &account = original_account_state(address).account();
    return account ? account->balance : 0;
}

bool State::record_balance_constraint_for_debit(
    Address const &address, uint256_t const &debit)
{
    // Sequential execution needs only the balance check, not constraints for
    // reconciling a speculative execution with earlier transactions.
    return get_balance(address) >= debit;
}

void State::set_original_nonce(Address const &, uint64_t)
{
    // Sequential execution validates the actual nonce, without merge repair.
}

MONAD_NAMESPACE_END
