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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/vm.hpp>

#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db, vm::VM &monad_vm)
    : db_{db}
    , vm_{monad_vm}
    , state_(std::make_unique<StateDeltas>())
{
}

std::optional<Account> BlockState::read_account(Address const &address)
{
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_);
        if (MONAD_LIKELY(state_->find(it, address))) {
            return it->second.account.second;
        }
    }
    // database
    {
        auto const result = db_.read_account(address);
        StateDeltas::const_accessor it{};
        state_->emplace(
            it,
            address,
            StateDelta{.account = {result, result}, .storage = {}});
        return it->second.account.second;
    }
}

bytes32_t BlockState::read_storage(
    Address const &address, Incarnation const incarnation, bytes32_t const &key)
{
    bool read_storage = false;
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_);
        MONAD_ASSERT(state_->find(it, address));
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            return {};
        }
        auto const &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            if (MONAD_LIKELY(storage.find(it2, key))) {
                return it2->second.second;
            }
        }
        auto const &orig_account = it->second.account.first;
        if (orig_account && incarnation == orig_account->incarnation) {
            read_storage = true;
        }
    }
    // database
    {
        bytes32_t result{};
        if (read_storage) {
            result = db_.read_storage(address, incarnation, key);
        }
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            return result;
        }
        auto &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            storage.emplace(it2, key, std::make_pair(result, result));
            return it2->second.second;
        }
    }
}

bool BlockState::can_merge(State &state) const
{
    MONAD_ASSERT(state_);
    auto const &original = state.original();
    for (auto const &kv : original) {
        Address const &address = kv.first;
        OriginalAccountState const &account_state = kv.second;
        auto const &account = account_state.account();
        auto const &storage = account_state.storage_;
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        if (account != it->second.account.second) {
            // RELAXED MERGE
            // try to fix original and current in `state` to match the block
            // state up until this transaction
            if (!state.try_fix_account_mismatch(
                    address, it->second.account.second)) {
                return false;
            }
        }
        // TODO account.has_value()???
        for (auto const &[key, value] : storage) {
            StorageDeltas::const_accessor it2{};
            if (it->second.storage.find(it2, key)) {
                if (value != it2->second.second) {
                    return false;
                }
            }
            else {
                if (value) {
                    return false;
                }
            }
        }
    }
    return true;
}

MONAD_NAMESPACE_END
