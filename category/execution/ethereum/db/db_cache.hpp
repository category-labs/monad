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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

// Encoding-agnostic LRU + proposal cache for accounts and storage leaves.
// Storage values are held in the same byte-shape that ProposalPostState uses:
// zeroless slot bytes for slot encoding, encoded-page bytes for page encoding.
// The cache itself does not interpret the bytes, TrieDb does, based on its
// compile-time `page_encoded` parameter.
class DbCache final
{
    using AddressHashCompare = BytesHashCompare<Address>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using AccountsCache =
        LruCache<Address, std::optional<Account>, AddressHashCompare>;
    using StorageCache =
        LruCache<StorageKey, byte_string, StorageKeyHashCompare>;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{10'000'000};
    Proposals proposals_;

public:
    DbCache() = default;

    bool
    try_read_account(Address const &address, std::optional<Account> &result)
    {
        auto const res = proposals_.try_read_account(address, result);
        if (res.found) {
            return true;
        }
        if (!res.truncated) {
            AccountsCache::ConstAccessor acc{};
            if (accounts_.find(acc, address)) {
                result = acc->second.value_;
                return true;
            }
        }
        return false;
    }

    bool try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, byte_string &result)
    {
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, result);
        if (res.found) {
            return true;
        }
        if (!res.truncated) {
            StorageKey const skey{address, incarnation, key};
            StorageCache::ConstAccessor acc{};
            if (storage_.find(acc, skey)) {
                result = acc->second.value_;
                return true;
            }
        }
        return false;
    }

    void
    set_block_and_prefix(uint64_t const block_number, bytes32_t const &block_id)
    {
        proposals_.set_block_and_prefix(block_number, block_id);
    }

    void update_proposal_state(
        ProposalPostState post_state, uint64_t const block_number,
        bytes32_t const &block_id)
    {
        proposals_.commit(std::move(post_state), block_number, block_id);
    }

    void on_finalize(uint64_t const block_number, bytes32_t const &block_id)
    {
        std::unique_ptr<ProposalState> const ps =
            proposals_.finalize(block_number, block_id);
        if (ps) {
            insert_in_lru_caches(ps->post_state());
        }
        else {
            // Finalizing a truncated proposal. Clear LRU caches.
            accounts_.clear();
            storage_.clear();
        }
    }

    std::string accounts_stats()
    {
        return accounts_.print_stats();
    }

    std::string storage_stats()
    {
        return storage_.print_stats();
    }

private:
    void insert_in_lru_caches(ProposalPostState const &post_state)
    {
        for (auto const &[addr, acct] : post_state.accounts) {
            accounts_.insert(addr, acct);
        }
        for (auto const &[sk, leaf] : post_state.storage) {
            storage_.insert(sk, leaf);
        }
    }
};

MONAD_NAMESPACE_END
