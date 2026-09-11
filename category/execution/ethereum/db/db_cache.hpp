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
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>
#include <category/vm/utils/lru_weight_cache.hpp>

#include <chrono>
#include <cstdint>
#include <format>
#include <memory>
#include <optional>
#include <string>
#include <vector>

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

// Encoding-agnostic LRU + proposal cache for accounts and storage leaves.
// Storage values are held as storage_page_t, keyed by the trie key the
// caller passes: slot_key (single slot at index 0) for slot encoding, or
// page_key (full page) for page encoding. The caller (TrieDb) decides the
// key and offset based on its encoding; the cache does not.
//
// The caches run in stamp mode: one hash map, two eviction lists. Live
// entries carry the consensus stamp and are promoted only at stamp
// application, so live-list order is stamp order and cached entries (stamped
// within CACHE_WINDOW_BLOCKS) are never eviction victims while the per-block
// caps keep the cached set below the physical capacity. Negative results
// ("this key holds nothing") sit on a count-budgeted negative list of the
// same map — a value transition flips the entry in place, so the two can
// never disagree and a deleted entry forgets its stamp.
class DbCache final
{
    using AddressHashCompare = BytesHashCompare<Address>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using AccountsCache =
        LruCache<Address, std::optional<Account>, AddressHashCompare>;
    // The cache is slot-granular: keyed by slot_key, the value is a
    // storage_page_t used as a single-slot container holding the value at
    // index 0 only. This will be compatible for future page-granular reads.
    using StorageCache = vm::utils::LruWeightCache<
        StorageKey, storage_page_t, StorageKeyHashCompare>;

    static constexpr uint32_t STORAGE_CACHE_MAX_BYTES = 1024u * 1024 * 1024;
    static constexpr size_t NEGATIVE_MAX_ENTRIES = 2'000'000;

    AccountsCache accounts_;
    StorageCache storage_;
    Proposals proposals_;

public:
    static constexpr size_t ACCOUNT_CACHE_MAX_ENTRIES = 10'000'000;

    // stamp_mode false = plain wall-clock LRU promotion (pre multi-block
    // cache behavior, for baseline measurement arms). The capacities are
    // overridable for tests that exercise eviction; production sizes must
    // exceed the fixed-window bounds (CACHE_WINDOW_BLOCKS x the per-block
    // caps) plus in-flight inserts.
    explicit DbCache(
        bool const stamp_mode = true,
        size_t const account_capacity = ACCOUNT_CACHE_MAX_ENTRIES,
        uint32_t const storage_capacity_bytes = STORAGE_CACHE_MAX_BYTES,
        size_t const negative_capacity = NEGATIVE_MAX_ENTRIES)
        : accounts_{account_capacity, stamp_mode, negative_capacity}
        , storage_{
              storage_capacity_bytes,
              std::chrono::milliseconds{200},
              stamp_mode,
              negative_capacity}
    {
    }

    // Bootstrap: apply one block's stamp log record, oldest block first —
    // its selected keys in selection order, then its deaths — to resident
    // entries, so the stamps and live-list order end identical to a
    // continuously running node's. A key that died and was recreated
    // inside the window is live now but must come back unstamped, exactly
    // as the live node's entry did when its value flipped.
    void rebuild_stamps(
        std::vector<Address> const &accounts,
        std::vector<StorageKey> const &storage,
        std::vector<Address> const &dead_accounts,
        std::vector<StorageKey> const &dead_storage, uint64_t const block)
    {
        apply_stamps(accounts, storage, block);
        for (auto const &addr : dead_accounts) {
            accounts_.clear_stamp(addr);
        }
        for (auto const &key : dead_storage) {
            storage_.clear_stamp(key);
        }
    }

    // Residency check (tests / debug): the entry is live and carries `stamp`.
    bool account_has_stamp(Address const &address, uint64_t const stamp)
    {
        AccountsCache::ConstAccessor acc{};
        return accounts_.find(acc, address) && !accounts_.is_negative(acc) &&
               accounts_.stamp_of(acc) == stamp;
    }

    bool storage_has_stamp(StorageKey const &key, uint64_t const stamp)
    {
        StorageCache::ConstAccessor acc{};
        return storage_.find(acc, key) && !storage_.is_negative(acc) &&
               storage_.stamp_of(acc) == stamp;
    }

    // The optional stamp output is the entry's consensus stamp as of the
    // current read prefix: the proposal overlay wins, else the resident
    // entry's stamp field; 0 (cold) when neither knows the key — losing a
    // stamp only overcharges.
    CacheReadStatus try_read_account(
        Address const &address, std::optional<Account> &result,
        uint64_t *const stamp = nullptr)
    {
        bool stamp_found = false;
        if (stamp != nullptr) {
            *stamp = 0;
            stamp_found =
                proposals_.try_read_account_stamp(address, *stamp).found;
        }
        auto const res = proposals_.try_read_account(address, result);
        if (res.found) {
            if (stamp != nullptr && !stamp_found) {
                AccountsCache::ConstAccessor acc{};
                if (accounts_.find(acc, address)) {
                    *stamp = accounts_.stamp_of(acc);
                }
            }
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        AccountsCache::ConstAccessor acc{};
        if (accounts_.find(acc, address)) {
            result = acc->second.value_;
            if (stamp != nullptr && !stamp_found) {
                *stamp = accounts_.stamp_of(acc);
            }
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    // Read-through: cache a finalized-consistent account fetched from disk
    // after a `MissResolved` read. A nullopt is a valid negative entry (the
    // account is absent at the finalized baseline); it lands on the negative
    // list, where it cannot displace warm entries.
    void insert_account(
        Address const &address, std::optional<Account> const &account)
    {
        accounts_.insert(address, account, !account.has_value());
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
        StorageKey const skey{address, incarnation, key};
        StorageCache::ConstAccessor acc{};
        if (storage_.find(acc, skey)) {
            result = acc->second.value_;
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    CacheReadStatus try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, uint8_t const slot_offset, bytes32_t &result,
        uint64_t *const stamp = nullptr)
    {
        StorageKey const skey{address, incarnation, key};
        bool stamp_found = false;
        if (stamp != nullptr) {
            *stamp = 0;
            stamp_found = proposals_.try_read_storage_stamp(skey, *stamp).found;
        }
        storage_page_t page;
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, page);
        if (res.found) {
            // slot_offset is 0 for slot encoding, the in-page offset for page.
            result = page[slot_offset];
            if (stamp != nullptr && !stamp_found) {
                StorageCache::ConstAccessor acc{};
                if (storage_.find(acc, skey)) {
                    *stamp = storage_.stamp_of(acc);
                }
            }
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        StorageCache::ConstAccessor acc{};
        if (storage_.find(acc, skey)) {
            result = acc->second.value_[slot_offset];
            if (stamp != nullptr && !stamp_found) {
                *stamp = storage_.stamp_of(acc);
            }
            return CacheReadStatus::Hit;
        }
        return CacheReadStatus::MissResolved;
    }

    // Read-through: insert a finalized-consistent storage page fetched from
    // disk after a `MissResolved` read. An empty page is a valid negative
    // entry. try_insert_no_overwrite leaves an entry a concurrent sibling
    // read already cached untouched (all concurrent read-throughs resolve
    // against the same finalized baseline, so a colliding entry holds the
    // same page anyway).
    void insert_storage_page(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, storage_page_t const &page)
    {
        StorageKey const skey{address, incarnation, key};
        storage_.try_insert_no_overwrite(
            skey,
            page,
            static_cast<uint32_t>(page.byte_size()),
            page.is_empty());
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
            apply_stamps(
                ps->post_state().account_stamps,
                ps->post_state().storage_stamps,
                block_number);
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
        for (auto const &[addr, acct] : post_state.accounts) {
            accounts_.insert(addr, acct, !acct.has_value());
        }
        for (auto const &[sk, leaf] : post_state.storage) {
            storage_.insert(
                sk,
                leaf,
                static_cast<uint32_t>(leaf.byte_size()),
                leaf.is_empty());
        }
    }

    // Stamp the block's selected entries in selection order and advance the
    // eviction floor. Every selected entry is live at the block's post-state
    // (selection excludes entries that die in the block) and resident (the
    // block's reads and writes put it there, and the LRU never evicts a
    // cached entry), so a missing entry is a residency bug.
    void apply_stamps(
        std::vector<Address> const &accounts,
        std::vector<StorageKey> const &storage, uint64_t const block)
    {
        for (auto const &addr : accounts) {
            bool const stamped = accounts_.set_stamp(addr, block);
            MONAD_ASSERT_PRINTF(
                stamped, "stamped account not resident at block %lu", block);
        }
        for (auto const &key : storage) {
            bool const stamped = storage_.set_stamp(key, block);
            MONAD_ASSERT_PRINTF(
                stamped,
                "stamped storage entry not resident at block %lu",
                block);
        }
        accounts_.set_evict_floor(cache_evict_floor(block));
        storage_.set_evict_floor(cache_evict_floor(block));
    }
};

MONAD_NAMESPACE_END
