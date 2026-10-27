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
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/fmt/state_deltas_fmt.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <quill/std/Optional.h>

#include <utility>

MONAD_NAMESPACE_BEGIN

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

void BlockState::merge(State const &state)
{
    ankerl::unordered_dense::segmented_set<bytes32_t> code_hashes;

    auto const &current = state.current();
    for (auto const &[address, stack] : current) {
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto const &account_state = stack.recent();
        if (!account_state.is_resolved()) {
            continue;
        }
        auto const &account = account_state.account();
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
    for (auto const &[address, stack] : current) {
        auto const &account_state = stack.recent();
        if (!account_state.is_resolved()) {
            continue;
        }
        auto const &account = account_state.account();
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
