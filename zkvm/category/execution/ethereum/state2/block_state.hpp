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

#include <category/core/assert.h>
#include <category/core/likely.h>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class State;

using SelfDestructStorageReads = ankerl::unordered_dense::segmented_map<
    Address, ankerl::unordered_dense::segmented_set<bytes32_t>>;

class BlockState final
{
    PartialTrieDb &db_;
    vm::VM &vm_;
    std::unique_ptr<StateDeltas> state_;
    Code code_;
    SelfDestructStorageReads self_destruct_storage_reads_;

public:
    BlockState(PartialTrieDb &db, vm::VM &monad_vm)
        : db_{db}
        , vm_{monad_vm}
        , state_(std::make_unique<StateDeltas>())
    {
    }

    vm::VM &vm()
    {
        return vm_;
    }

    // Sets resolved on every return. Nullopt with resolved == true is proven
    // absence; resolved == false means missing witness data.
    std::optional<Account> read_account(Address const &address, bool &resolved)
    {
        resolved = true;
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
            auto const result = db_.try_read_account(address);
            if (MONAD_UNLIKELY(!result)) {
                resolved = false;
                return std::nullopt;
            }
            StateDeltas::const_accessor it{};
            state_->emplace(
                it,
                address,
                StateDelta{.account = {*result, *result}, .storage = {}});
            return it->second.account.second;
        }
    }

    std::optional<bytes32_t> try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key)
    {
        bool read_storage = false;
        // block state
        {
            StateDeltas::const_accessor it{};
            MONAD_ASSERT(state_);
            MONAD_ASSERT(state_->find(it, address));
            auto const &account = it->second.account.second;
            if (!account || incarnation != account->incarnation) {
                return bytes32_t{};
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
                auto const value = db_.try_read_storage(address, key);
                if (MONAD_UNLIKELY(!value)) {
                    return std::nullopt;
                }
                result = *value;
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

    bytes32_t read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key)
    {
        auto const value = try_read_storage(address, incarnation, key);
        MONAD_ASSERT(value.has_value());
        return *value;
    }

    vm::SharedVarcode read_code(bytes32_t const &);

    [[gnu::always_inline]] bool can_merge(State &) const
    {
        // Sequential execution cannot conflict with another transaction.
        return true;
    }

    void merge(State const &);

    struct ReleasedState
    {
        std::unique_ptr<StateDeltas> state;
        Code code;
        SelfDestructStorageReads self_destruct_storage_reads;
    };

    ReleasedState release() &&;

    void log_debug();
};

MONAD_NAMESPACE_END
