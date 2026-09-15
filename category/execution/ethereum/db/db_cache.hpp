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
#include <category/execution/monad/db/stamp_cache.hpp>
#include <category/execution/monad/db/stamp_index.hpp>
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
// Protocol entries use one eviction list: stamped values, stale values, then
// empty entries. Consensus stamps are independent of the ordinary LRU's clock.
// Historical charges bound selections; rejected growth can exceed that bound.
// Physical cache capacities; smaller values support eviction tests.
struct DbCacheSizes
{
    size_t account_entries{10'000'000};
    uint32_t storage_bytes{1024u * 1024 * 1024};
    size_t negative_entries{2'000'000};
};

class DbCache final
{
    using AddressHashCompare = BytesHashCompare<Address>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using LegacyAccounts =
        LruCache<Address, std::optional<Account>, AddressHashCompare>;
    using AccountsCache =
        StampCache<Address, std::optional<Account>, AddressHashCompare>;

    using LegacyStorage = vm::utils::LruWeightCache<
        StorageKey, storage_page_t, StorageKeyHashCompare>;
    using StorageCache =
        StampCache<StorageKey, storage_page_t, StorageKeyHashCompare>;

    static constexpr uint32_t STORAGE_CACHE_MAX_BYTES = 1024u * 1024 * 1024;
    static constexpr size_t NEGATIVE_MAX_ENTRIES = 2'000'000;

    AccountsCache accounts_;
    StorageCache storage_;
    std::unique_ptr<LegacyAccounts> legacy_accounts_;
    std::unique_ptr<LegacyStorage> legacy_storage_;
    StampIndex<Address> account_history_;
    StampIndex<StorageKey, StorageKeyHashCompare> storage_history_;
    Proposals proposals_;
    bool const stamp_mode_;

public:
    static constexpr size_t ACCOUNT_CACHE_MAX_ENTRIES = 10'000'000;

    // stamp_mode false = plain wall-clock LRU promotion (pre multi-block
    // cache behavior). The capacities are
    // overridable for tests. Production capacities must hold the protocol
    // eligible set, including any uncharged growth.
    explicit DbCache(
        bool const stamp_mode = true,
        size_t const account_capacity = ACCOUNT_CACHE_MAX_ENTRIES,
        uint32_t const storage_capacity_bytes = STORAGE_CACHE_MAX_BYTES,
        size_t const negative_capacity = NEGATIVE_MAX_ENTRIES)
        : accounts_{account_capacity, account_capacity, negative_capacity}
        , storage_{storage_capacity_bytes, ACCOUNT_CACHE_MAX_ENTRIES, negative_capacity}
        , legacy_accounts_{stamp_mode ? nullptr : std::make_unique<LegacyAccounts>(account_capacity)}
        , legacy_storage_{stamp_mode ? nullptr : std::make_unique<LegacyStorage>(storage_capacity_bytes)}
        , stamp_mode_{stamp_mode}
    {
    }

    DbCache(bool const stamp_mode, DbCacheSizes const &sizes)
        : DbCache{
              stamp_mode,
              sizes.account_entries,
              sizes.storage_bytes,
              sizes.negative_entries}
    {
    }

    // Bootstrap and finalization share the same full-value installation path.
    void rebuild_stamps(ProposalPostState const &post)
    {
        accounts_.clear();
        storage_.clear();
        account_history_.clear();
        storage_history_.clear();
        install(post);
    }

    // Residency check (tests / debug): the entry is resident with `stamp`.
    bool account_has_stamp(Address const &address, uint64_t const stamp)
    {
        AccountsCache::ConstAccessor acc{};
        return accounts_.find(acc, address) && accounts_.stamp_of(acc) == stamp;
    }

    bool storage_has_stamp(StorageKey const &key, uint64_t const stamp)
    {
        StorageCache::ConstAccessor acc{};
        return storage_.find(acc, key) && storage_.stamp_of(acc) == stamp;
    }

    // The optional stamp output is the entry's consensus stamp as of the
    // current read prefix: the proposal overlay wins, else finalized key
    // history. Empty values keep their historical stamp but are not eligible.
    CacheReadStatus try_read_account(
        Address const &address, std::optional<Account> &result,
        uint64_t *const stamp = nullptr)
    {
        if (stamp != nullptr) {
            *stamp = 0;
            auto const known =
                proposals_.try_read_account_stamp(address, *stamp);
            if (known.truncated) {
                *stamp = CACHE_STAMP_UNKNOWN;
            }
            else if (!known.found) {
                *stamp = account_history_.find(address);
            }
        }
        auto const res = proposals_.try_read_account(address, result);
        if (res.found) {
            return CacheReadStatus::Hit;
        }
        if (res.truncated) {
            return CacheReadStatus::MissTruncated;
        }
        if (!stamp_mode_) {
            LegacyAccounts::ConstAccessor acc;
            if (!legacy_accounts_->find(acc, address)) {
                return CacheReadStatus::MissResolved;
            }
            result = acc->second.value_;
            return CacheReadStatus::Hit;
        }
        AccountsCache::ConstAccessor acc{};
        if (accounts_.find(acc, address)) {
            result = acc->second.value_;
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
        if (!stamp_mode_) {
            legacy_accounts_->insert(address, account);
        }
        else if (!account) {
            accounts_.insert(address, account, 1, true);
        }
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
        if (!stamp_mode_) {
            LegacyStorage::ConstAccessor acc;
            if (!legacy_storage_->find(acc, skey)) {
                return CacheReadStatus::MissResolved;
            }
            result = acc->second.value_;
            return CacheReadStatus::Hit;
        }
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
        if (stamp != nullptr) {
            *stamp = 0;
            auto const known = proposals_.try_read_storage_stamp(skey, *stamp);
            if (known.truncated) {
                *stamp = CACHE_STAMP_UNKNOWN;
            }
            else if (!known.found) {
                *stamp = storage_history_.find(skey);
            }
        }
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
        if (!stamp_mode_) {
            LegacyStorage::ConstAccessor acc;
            if (!legacy_storage_->find(acc, skey)) {
                return CacheReadStatus::MissResolved;
            }
            result = acc->second.value_[slot_offset];
            return CacheReadStatus::Hit;
        }
        StorageCache::ConstAccessor acc{};
        if (storage_.find(acc, skey)) {
            result = acc->second.value_[slot_offset];
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
        if (!stamp_mode_) {
            legacy_storage_->try_insert_no_overwrite(
                skey, page, static_cast<uint32_t>(page.byte_size()));
        }
        else if (page.is_empty()) {
            storage_.insert(
                skey, page, static_cast<uint32_t>(page.byte_size()), true);
        }
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

    bool on_finalize(uint64_t const block_number, bytes32_t const &block_id)
    {
        std::unique_ptr<ProposalState> const ps =
            proposals_.finalize(block_number, block_id);
        if (ps) {
            install(ps->post_state());
        }
        else {
            // Finalizing a truncated proposal. Clear LRU caches.  This is an
            // expensive operation. However, with 100 unfinalized proposals,
            // cache speed is the least of our problems.
            accounts_.clear();
            storage_.clear();
            account_history_.clear();
            storage_history_.clear();
            if (!stamp_mode_) {
                legacy_accounts_->clear();
                legacy_storage_->clear();
            }
        }
        return !ps && stamp_mode_;
    }

    std::string accounts_stats()
    {
        return stamp_mode_ ? std::format("{:8}", accounts_.size())
                           : legacy_accounts_->print_stats();
    }

    std::string storage_stats()
    {
        return std::format(
            "{:8} / {:10}",
            stamp_mode_ ? storage_.size() : legacy_storage_->size(),
            stamp_mode_ ? storage_.approx_weight()
                        : legacy_storage_->approx_weight());
    }

private:
    void install(ProposalPostState const &post)
    {
        if (!stamp_mode_) {
            for (auto const &[key, value] : post.accounts) {
                legacy_accounts_->insert(key, value);
            }
            for (auto const &[key, value] : post.storage) {
                legacy_storage_->insert(
                    key, value, static_cast<uint32_t>(value.byte_size()));
            }
            return;
        }
        if (post.cache_updated) {
            accounts_.set_evict_floor(post.cache_pricing.accounts.floor);
            storage_.set_evict_floor(post.cache_pricing.storage.floor);
            account_history_.update(post.cache_pricing.accounts, post.account_stamps);
            storage_history_.update(post.cache_pricing.storage, post.storage_stamps);
        }
        // Install touched eligible values even when re-entry follows eviction
        // of a negative value. The independent index supplies the old stamp.
        std::vector<std::pair<uint64_t, Address>> accounts;
        for (auto const &[key, value] : post.accounts) {
            auto const stamp = account_history_.find(key);
            if (stamp && value) {
                accounts.emplace_back(stamp, key);
                continue;
            }
            bool resident;
            {
                AccountsCache::ConstAccessor acc;
                resident = accounts_.find(acc, key);
            }
            if (!value || resident) {
                accounts_.insert(key, value, 1, !value);
            }
        }
        std::sort(accounts.begin(), accounts.end());
        for (auto const &[stamp, key] : accounts) {
            accounts_.insert(key, post.accounts.at(key), 1, false, stamp);
        }
        std::vector<std::pair<uint64_t, StorageKey>> storage;
        for (auto const &[key, value] : post.storage) {
            auto const stamp = storage_history_.find(key);
            if (stamp && !value.is_empty()) {
                storage.emplace_back(stamp, key);
                continue;
            }
            bool resident;
            {
                StorageCache::ConstAccessor acc;
                resident = storage_.find(acc, key);
            }
            if (value.is_empty() || resident) {
                storage_.insert(key, value,
                    static_cast<uint32_t>(value.byte_size()), value.is_empty());
            }
        }
        std::sort(storage.begin(), storage.end(), [](auto const &a, auto const &b) {
            return a.first < b.first;
        });
        for (auto const &[stamp, key] : storage) {
            auto const &value = post.storage.at(key);
            storage_.insert(key, value,
                static_cast<uint32_t>(value.byte_size()), false, stamp);
        }
    }
};

MONAD_NAMESPACE_END
