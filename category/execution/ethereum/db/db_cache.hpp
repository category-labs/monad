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
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>
#include <category/vm/utils/lru_weight_cache.hpp>

#include <cstdint>
#include <cstring>
#include <format>
#include <memory>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

// Outcome of a cache read.
enum class CacheReadStatus
{
    Hit, // served from proposal map or LRU
    MissResolved, // both missed, proposal chain walked to the finalized base
                  // -> disk value == finalized value -> safe to cache this miss
    MissTruncated, // proposal chain truncated before the finalized base
                   // -> can't prove finalized-consistent -> don't cache miss
};

// A storage_ entry. storage_ is keyed by StorageKey with a zero incarnation,
// the way the trie has no incarnation, so an address's page has one entry
// across incarnations. `incarnation` is the one the page data belongs to, and
// a read hits only for that incarnation. `stamp` and `size` are the page
// cache's membership fields, meaningful only while the entry is protected in
// storage_, and never touched by reads.
struct StorageCacheEntry
{
    storage_page_t page;
    Incarnation incarnation{0, 0};
    uint64_t stamp{0};
    uint64_t size{0};
};

// Encoding-agnostic LRU + proposal cache for accounts and storage leaves.
// Storage values are held as storage_page_t, keyed by the trie key the
// caller passes: slot_key (single slot at index 0) for slot encoding, or
// page_key (full page) for page encoding. The caller (TrieDb) decides the
// key and offset based on its encoding; the cache does not.
class DbCache final
{
    using AddressHashCompare = BytesHashCompare<Address>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using AccountsCache =
        LruCache<Address, std::optional<Account>, AddressHashCompare>;
    // Keyed by the trie key the caller passes: slot_key on slot-encoded
    // databases, where the page holds the value at index 0 only, and
    // page_key on page-encoded ones.
    using StorageCache = vm::utils::LruWeightCache<
        StorageKey, StorageCacheEntry, StorageKeyHashCompare>;

    static constexpr uint32_t STORAGE_CACHE_MAX_BYTES = 256u * 1024 * 1024;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{STORAGE_CACHE_MAX_BYTES};
    Proposals proposals_;

public:
    DbCache() = default;

    CacheReadStatus
    try_read_account(Address const &address, std::optional<Account> &result)
    {
        auto const res = proposals_.try_read_account(address, result);
        if (res.found) {
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        AccountsCache::ConstAccessor acc{};
        if (accounts_.find(acc, address)) {
            result = acc->second.value_;
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    // Read-through: cache a finalized-consistent account fetched from disk
    // after a `MissResolved` read. A nullopt is a valid (negative) entry: it
    // records that the account is absent at the finalized baseline.
    void insert_account(
        Address const &address, std::optional<Account> const &account)
    {
        accounts_.insert(address, account);
    }

    CacheReadStatus try_read_storage_page(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, storage_page_t &result)
    {
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, result);
        if (res.found) {
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        StorageCache::ConstAccessor acc{};
        if (storage_.find(acc, storage_cache_key(address, key)) &&
            serves(acc->second.value_, incarnation)) {
            result = acc->second.value_.page;
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    CacheReadStatus try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, uint8_t const slot_offset, bytes32_t &result)
    {
        storage_page_t page;
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, page);
        if (res.found) {
            // slot_offset is 0 for slot encoding, the in-page offset for page.
            result = page[slot_offset];
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        StorageCache::ConstAccessor acc{};
        if (storage_.find(acc, storage_cache_key(address, key)) &&
            serves(acc->second.value_, incarnation)) {
            result = acc->second.value_.page[slot_offset];
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    // Read-through: insert a finalized-consistent storage page fetched from
    // disk after a `MissResolved` read, linked as the newest unprotected
    // entry. try_insert_no_overwrite leaves any existing entry untouched: a
    // concurrent sibling read already cached the same page, or the entry is
    // protected, or it holds another incarnation's data, which only costs
    // hits until finalization or eviction replaces it.
    void insert_storage_page(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, storage_page_t const &page)
    {
        storage_.try_insert_no_overwrite(
            storage_cache_key(address, key),
            StorageCacheEntry{.page = page, .incarnation = incarnation},
            static_cast<uint32_t>(page.byte_size()));
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
    static StorageKey
    storage_cache_key(Address const &address, bytes32_t const &key)
    {
        return StorageKey{address, Incarnation{0, 0}, key};
    }

    static bool
    serves(StorageCacheEntry const &entry, Incarnation const incarnation)
    {
        return entry.incarnation.to_int() == incarnation.to_int();
    }

    void insert_in_lru_caches(ProposalPostState const &post_state)
    {
        for (auto const &[addr, acct] : post_state.accounts) {
            accounts_.insert(addr, acct);
        }
        for (auto const &[sk, leaf] : post_state.storage) {
            Address address;
            Incarnation incarnation{0, 0};
            bytes32_t key;
            std::memcpy(address.bytes, sk.bytes, sizeof(Address));
            std::memcpy(
                &incarnation, sk.bytes + sizeof(Address), sizeof(Incarnation));
            std::memcpy(
                key.bytes,
                sk.bytes + sizeof(Address) + sizeof(Incarnation),
                sizeof(bytes32_t));
            StorageKey const cache_key = storage_cache_key(address, key);
            StorageCacheEntry entry{.page = leaf, .incarnation = incarnation};
            // Keep the membership fields of an entry the page cache holds.
            {
                StorageCache::ConstAccessor acc{};
                if (storage_.find(acc, cache_key)) {
                    entry.stamp = acc->second.value_.stamp;
                    entry.size = acc->second.value_.size;
                }
            }
            storage_.insert(
                cache_key, entry, static_cast<uint32_t>(leaf.byte_size()));
        }
    }
};

MONAD_NAMESPACE_END
