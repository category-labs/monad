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

#include <category/execution/ethereum/state3/state.hpp>

MONAD_NAMESPACE_BEGIN

// Share cache traversal and incarnation handling while letting the caller
// choose a strict or fallible block-state read and cache only successful reads.
template <typename OnMiss>
auto State::get_storage_impl(
    Address const &address, bytes32_t const &key, OnMiss &&on_miss)
    -> std::invoke_result_t<OnMiss, AccountState::StorageMap &, Incarnation>
{
    auto const it = current_.find(address);
    if (it == current_.end()) {
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &account_state = it2->second;
        auto const &account = account_state.account();
        MONAD_ASSERT(account.has_value());
        auto &storage = account_state.storage_;
        if (auto const *const it3 = storage.find(key); it3) {
            return *it3;
        }
        else {
            return on_miss(storage, account.value().incarnation);
        }
    }
    else {
        auto const &account_state = it->second.recent();
        auto const &account = account_state.account();
        MONAD_ASSERT(account.has_value());
        auto const &storage = account_state.storage_;
        if (auto const *const it2 = storage.find(key); it2) {
            return *it2;
        }
        auto const it2 = original_.find(address);
        MONAD_ASSERT(it2 != original_.end());
        auto &original_account_state = it2->second;
        auto const &original_account = original_account_state.account();
        if (!original_account.has_value() ||
            account.value().incarnation !=
                original_account.value().incarnation) {
            return bytes32_t{};
        }
        auto &original_storage = original_account_state.storage_;
        if (auto const *const it3 = original_storage.find(key); it3) {
            return *it3;
        }
        else {
            return on_miss(original_storage, account.value().incarnation);
        }
    }
}

MONAD_NAMESPACE_END
