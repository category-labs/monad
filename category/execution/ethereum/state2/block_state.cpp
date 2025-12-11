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
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
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

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db, vm::VM &monad_vm)
    : db_{db}
    , vm_{monad_vm}
    , state_(std::make_unique<StateDeltas>())
    , final_state_(std::make_unique<StateDeltas>())
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
        auto const result = read_storage
                                ? db_.read_storage(address, incarnation, key)
                                : bytes32_t{};
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

void BlockState::merge(State const &state)
{
    ankerl::unordered_dense::segmented_set<bytes32_t> code_hashes;

    auto const &current = state.current();
    for (auto const &[address, stack] : current) {
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        if (account.has_value()) {
            code_hashes.insert(account.value().code_hash);
        }
    }

    auto const &code = state.code();
    for (auto const &code_hash : code_hashes) {
        auto const it = code.find(code_hash);
        if (it == code.end()) {
            continue;
        }
        code_.emplace(code_hash, it->second->intercode()); // TODO try_emplace
    }

    MONAD_ASSERT(state_);
    MONAD_ASSERT(final_state_);
    for (auto const &[address, stack] : current) {
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        it->second.account.second = account;
        StateDeltas::accessor final_it{};
        if (final_state_->find(final_it, address)) {
            MONAD_ASSERT(
                final_it->second.account.first == it->second.account.first);
            final_it->second.account.second = account;
        }
        else {
            final_state_->emplace(
                final_it,
                address,
                StateDelta{.account = it->second.account, .storage = {}});
        }
        if (account.has_value()) {
            for (auto const &[key, value] : storage) {
                StorageDeltas::accessor it2{};
                if (it->second.storage.find(it2, key)) {
                    it2->second.second = value;
                }
                else {
                    it->second.storage.emplace(
                        it2, key, std::make_pair(bytes32_t{}, value));
                }
                StorageDeltas::accessor final_it2{};
                if (final_it->second.storage.find(final_it2, key)) {
                    final_it2->second.second = value;
                }
                else {
                    final_it->second.storage.emplace(key, it2->second);
                }
            }
        }
        else {
            it->second.storage.clear();
            final_it->second.storage.clear();
        }
    }
}

void BlockState::commit(
    bytes32_t const &block_id, BlockHeader const &header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    db_.commit(
        std::move(final_state_),
        code_,
        block_id,
        header,
        receipts,
        call_frames,
        senders,
        transactions,
        ommers,
        withdrawals);
}

void BlockState::log_debug()
{
    MONAD_ASSERT(state_);
    LOG_DEBUG("State Deltas: {}", *state_);
    LOG_DEBUG("Final States: {}", *final_state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
