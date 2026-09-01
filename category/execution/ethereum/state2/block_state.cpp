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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/fmt/state_deltas_fmt.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <quill/std/Optional.h>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db, vm::VM &monad_vm, Db *const secondary_db)
    : db_{db}
    , secondary_db_{secondary_db}
    , vm_{monad_vm}
    , state_(std::make_unique<StateDeltas>())
{
#ifdef MONAD_ZKVM_ZISK
    // Reserve initial capacity to avoid early rehashes.
    // Host TBB maps have no reserve().
    state_->reserve(1024);
    code_.reserve(1024);
#endif
}

#ifdef MONAD_ZKVM_ZISK
StateDelta &BlockState::read_account_delta(Address const &address)
{
    // Find or insert in one lookup; read the DB only when creating an entry.
    struct Read
    {
        Db &db;
        Address const &address;

        operator StateDelta() const
        {
            auto const result = db.read_account(address);
            return StateDelta{.account = {result, result}, .storage = {}};
        }
    };

    MONAD_ASSERT(state_);
    return state_->try_emplace(address, Read{db_, address}).first->second;
}
#endif

std::optional<Account> BlockState::read_account(Address const &address)
{
#ifdef MONAD_ZKVM_ZISK
    return read_account_delta(address).account.second;
#else
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
#endif
}

#ifdef MONAD_ZKVM_ZISK
bytes32_t const &BlockState::read_storage(
    StateDelta &delta, Address const &address, Incarnation const incarnation,
    bytes32_t const &key)
{
    // Keep using the supplied entry across the DB read: guest execution is
    // single-threaded, and map insertions preserve pointers.
    auto const &account = delta.account.second;
    if (!account || incarnation != account->incarnation) {
        // A returned reference must outlive this call.
        static constexpr bytes32_t zero{};
        return zero;
    }
    // The single-threaded guest cannot change the account during the DB read,
    // so it does not need the host's second account check.
    auto const &orig_account = delta.account.first;
    // Reserve for 64 slots on the first read to avoid early rehashes.
    if (MONAD_UNLIKELY(delta.storage.bucket_count() == 0)) {
        delta.storage.reserve(64);
    }

    // Defer the DB read until try_emplace constructs a missing slot.
    struct Read
    {
        BlockState &self;
        Address const &address;
        Incarnation incarnation;
        bytes32_t const &key;
        bool in_db;

        // Initialize directly from the DB result instead of zeroing then assigning.
        operator StorageDelta() const
        {
            if (!in_db) {
                return {};
            }
            bytes32_t const result =
                self.db_.read_storage(address, incarnation, key);
            MONAD_ASSERT(
                !self.secondary_db_ ||
                self.secondary_db_->read_storage(address, incarnation, key) ==
                    result);
            return {result, result};
        }
    };

    // Find or insert in one lookup; an existing slot never converts Read.
    return delta.storage
        .try_emplace(
            key,
            Read{
                *this,
                address,
                incarnation,
                key,
                orig_account && incarnation == orig_account->incarnation})
        .first->second.second;
}
#endif

bytes32_t BlockState::read_storage(
    Address const &address, Incarnation const incarnation, bytes32_t const &key)
{
#ifdef MONAD_ZKVM_ZISK
    StateDeltas::accessor it{};
    MONAD_ASSERT(state_);
    MONAD_ASSERT(state_->find(it, address));
    return read_storage(it->second, address, incarnation, key);
#else
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
            MONAD_ASSERT(
                !secondary_db_ || secondary_db_->read_storage(
                                      address, incarnation, key) == result);
        }
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        // The host must recheck the account after releasing the lock for the read.
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
#endif
}

vm::SharedVarcode BlockState::read_code(bytes32_t const &code_hash)
{
    // vm
    if (auto vcode = vm_.find_varcode(code_hash)) {
        return *vcode;
    }
    // block state
    {
        Code::const_accessor it{};
        if (code_.find(it, code_hash)) {
            return vm_.try_insert_varcode(code_hash, it->second);
        }
    }
    // database
    {
        auto const result = db_.read_code(code_hash);
        MONAD_ASSERT(result);
        MONAD_ASSERT_PRINTF(
            code_hash == NULL_HASH || result->size() != 0,
            "code_hash %s, code size %zu, block_number %lu",
            fmt::format("{}", code_hash).c_str(),
            result->size(),
            db_.get_block_number());
        return vm_.try_insert_varcode(code_hash, result);
    }
}

bool BlockState::can_merge(State &state) const
{
    MONAD_ASSERT(state_);
    auto const &original = state.original();
    for (auto &kv : original) {
        Address const &address = kv.first;
        OriginalAccountState const &account_state = kv.second;
        auto const &account = account_state.account_;
        // Validate cached original slot values; the inherited storage_ is
        // empty.
        auto const &storage = account_state.prestate_storage_;
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

void BlockState::merge(State const &state)
{
    // Merge code directly: code_.emplace ignores duplicate keys, avoiding
    // a separate set of distinct code hashes for each transaction.
    auto const &current = state.current();
    auto const &code = state.code();
    for (auto const &[address, account_state] : current) {
#ifdef MONAD_ZKVM_ZISK
        // No code to merge: skip all account lookups in this loop.
        // Account and storage changes are merged by the next loop.
        if (code.empty()) {
            break;
        }
#endif
        auto const &account = account_state.account_;
        if (account.has_value()) {
            auto const it = code.find(account.value().code_hash);
            if (it != code.end()) {
                code_.emplace(
                    account.value().code_hash,
                    it->second->intercode()); // TODO try_emplace
            }
        }
    }

    MONAD_ASSERT(state_);
    for (auto const &[address, account_state] : current) {
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
#ifdef MONAD_ZKVM_ZISK
        // The entry the account's original row was read from.
        MONAD_ASSERT(account_state.orig_ != nullptr);
        StateDelta *const cached_delta = account_state.orig_->delta_;
        MONAD_ASSERT(cached_delta != nullptr);
        StateDelta &delta = *cached_delta;
#else
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        StateDelta &delta = it->second;
#endif
        delta.account.second = account;
        if (account.has_value()) {
            for (auto const &[key, value] : storage) {
                StorageDeltas::accessor it2{};
                if (delta.storage.find(it2, key)) {
                    it2->second.second = value;
                }
                else {
#ifdef MONAD_ZKVM_ZISK
                    // Match read_storage's initial capacity when merge
                    // inserts the first slot. Host TBB maps have no reserve().
                    if (MONAD_UNLIKELY(delta.storage.empty())) {
                        delta.storage.reserve(64);
                    }
#endif
                    delta.storage.emplace(
                        key, std::make_pair(bytes32_t{}, value));
                }
            }
        }
        else {
            if (delta.account.first.has_value()) {
                auto const [iter, inserted] =
                    self_destruct_storage_reads_.try_emplace(address);
                if (inserted) {
                    for (auto const &kv : delta.storage) {
                        iter->second.insert(kv.first);
                    }
                }
            }
            delta.storage.clear();
        }
    }
}

BlockState::ReleasedState BlockState::release() &&
{
    return {
        std::move(state_),
        std::move(code_),
        std::move(self_destruct_storage_reads_)};
}

void BlockState::log_debug()
{
    MONAD_ASSERT(state_);
    LOG_DEBUG("State Deltas: {}", *state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
