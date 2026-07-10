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
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/account_key.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>
#include <category/vm/utils/lru_weight_cache.hpp>

#include <cstdint>
#include <format>
#include <memory>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

// Encoding-agnostic LRU + proposal cache for accounts and storage leaves.
// Storage values are held as storage_page_t, keyed by the trie key the
// caller passes: slot_key (single slot at index 0) for slot encoding, or
// page_key (full page) for page encoding. The caller (TrieDb) decides the
// key and offset based on its encoding; the cache does not.
class DbCache final
{
    using AccountKeyHashCompare = BytesHashCompare<AccountKey>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using AccountsCache =
        LruCache<AccountKey, std::optional<Account>, AccountKeyHashCompare>;
    // The cache is slot-granular: keyed by slot_key, the value is a
    // storage_page_t used as a single-slot container holding the value at
    // index 0 only. This will be compatible for future page-granular reads.
    using StorageCache = vm::utils::LruWeightCache<
        StorageKey, storage_page_t, StorageKeyHashCompare>;

    static constexpr uint32_t STORAGE_CACHE_MAX_BYTES = 256u * 1024 * 1024;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{STORAGE_CACHE_MAX_BYTES};
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
            if (accounts_.find(acc, AccountKey{address, std::nullopt})) {
                result = acc->second.value_;
                return true;
            }
        }
        return false;
    }

    bool try_read_storage_page(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, storage_page_t &result)
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

    bool try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, uint8_t const slot_offset, bytes32_t &result)
    {
        storage_page_t page;
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, page);
        if (res.found) {
            // slot_offset is 0 for slot encoding, the in-page offset for page.
            result = page[slot_offset];
            return true;
        }
        if (!res.truncated) {
            StorageKey const skey{address, incarnation, key};
            StorageCache::ConstAccessor acc{};
            if (storage_.find(acc, skey)) {
                result = acc->second.value_[slot_offset];
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

    void update_proposal_post_state(
        ProposalPostState post_state, std::optional<uint64_t> const &ns,
        uint64_t const block_number, bytes32_t const &block_id)
    {
        proposals_.commit(std::move(post_state), ns, block_number, block_id);
    }

    void on_finalize(uint64_t const block_number, bytes32_t const &block_id)
    {
        std::unique_ptr<ProposalState> const ps =
            proposals_.finalize(block_number, block_id);
        if (ps) {
            insert_in_lru_caches(ps->post_state());
        }
        else {
            // Finalizing a truncated proposal. Clear LRU caches.  This is an
            // expensive operation. However, with 100 unfinalized proposals,
            // cache speed is the least of our problems.
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
        return std::format(
            "{:8} / {:10}", storage_.size(), storage_.approx_weight());
    }

private:
    void insert_in_lru_caches(ProposalPostState const &post_state)
    {
        for (auto const &[key, acct] : post_state.accounts) {
            accounts_.insert(key, acct);
        }
        for (auto const &[sk, leaf] : post_state.storage) {
            storage_.insert(sk, leaf, static_cast<uint32_t>(leaf.byte_size()));
        }
    }
};

MONAD_NAMESPACE_END
