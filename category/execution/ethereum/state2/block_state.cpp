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
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/fmt/state_deltas_fmt.hpp> // NOLINT
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
    // Both maps take one entry per account or code the block touches and start
    // empty. Floors, not estimates: they skip the first several doublings,
    // which is where nearly all the growth events are, and a block that goes
    // past them pays one rehash.
    //
    // Guest only: on the node these are TBB concurrent_hash_maps, which size
    // through rehash() and have no reserve().
    state_->reserve(1024);
    code_.reserve(256);
#endif
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
            MONAD_ASSERT(
                !secondary_db_ || secondary_db_->read_storage(
                                      address, incarnation, key) == result);
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
        // The ORIGINAL row's slot cache lives in prestate_storage_ now, not in the base's
        // storage_ -- which is empty on an original row. Reading the base here would make
        // the loop below iterate nothing and this check pass unconditionally.
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
    // One pass, no dedup set. A set was built here to visit each distinct code
    // hash once, but code_.emplace already does nothing when the key is
    // present, so a duplicate costs one more find and one more no-op emplace --
    // against a whole hash set built from empty on every merge, 233 times a
    // block, hashing a 32-byte key per insert to deduplicate the handful of
    // accounts a transaction touches.
    //
    // The "no frame is open" invariant the removed loop asserted per row is
    // asserted once, on the undo log, inside State -- the only place that can
    // see it.
    auto const &current = state.current();
    auto const &code = state.code();
    for (auto const &[address, account_state] : current) {
        auto const &account = account_state.account_;
        if (!account.has_value()) {
            continue;
        }
        auto const it = code.find(account.value().code_hash);
        if (it == code.end()) {
            continue;
        }
        code_.emplace(
            account.value().code_hash,
            it->second->intercode()); // TODO try_emplace
    }

    MONAD_ASSERT(state_);
    for (auto const &[address, account_state] : current) {
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        it->second.account.second = account;
        if (account.has_value()) {
            for (auto const &[key, value] : storage) {
                StorageDeltas::accessor it2{};
                if (it->second.storage.find(it2, key)) {
                    it2->second.second = value;
                }
                else {
#ifdef MONAD_ZKVM_ZISK
                    // Floored on the first insert: this map starts empty for
                    // every account the block touches, and with a bump
                    // allocator each doubling is allocated, copied forward and
                    // abandoned -- and a rehash recomputes every key it holds.
                    //
                    // Guest only: on the node StorageDeltas is a TBB
                    // concurrent_hash_map, which sizes through rehash() and has
                    // no reserve().
                    if (MONAD_UNLIKELY(it->second.storage.empty())) {
                        it->second.storage.reserve(8);
                    }
#endif
                    it->second.storage.emplace(
                        key, std::make_pair(bytes32_t{}, value));
                }
            }
        }
        else {
            if (it->second.account.first.has_value()) {
                auto const [iter, inserted] =
                    self_destruct_storage_reads_.try_emplace(address);
                if (inserted) {
                    for (auto const &kv : it->second.storage) {
                        iter->second.insert(kv.first);
                    }
                }
            }
            it->second.storage.clear();
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
