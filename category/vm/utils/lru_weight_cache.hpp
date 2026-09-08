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

#include <category/core/assert.h>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <string>
#include <utility>

#include <unordered_set>

namespace monad::vm::utils
{
    // LRU Cache in which elements can have different weights. It is based
    // on the LruCache in monad.
    template <
        class Key, class Value,
        class KeyHashCompare = tbb::tbb_hash_compare<Key>>
    class LruWeightCache
    {
        /// TYPES
        class LruList;
        struct HashMapValue;
        using ListNode = std::pair<Key const, HashMapValue>;
        using HashMap =
            tbb::concurrent_hash_map<Key, HashMapValue, KeyHashCompare>;
        using Accessor = HashMap::accessor;

        /// DATA
        uint32_t max_weight_;
        std::atomic<int64_t> weight_;
        LruList lru_;
        HashMap hmap_;
        // Stamp mode: the entry time field holds the consensus stamp of live
        // entries, written only by set_stamp at finalize — find() never
        // writes it. Negative entries reuse the field as a local
        // last-promotion block via promote_negative. Entries whose value
        // satisfies pinned_ and whose stamp >= the pin floor never evict.
        bool const stamp_mode_{false};
        bool (*const pinned_)(Value const &){nullptr};
        std::atomic<uint64_t> pin_floor_{0};

    public:
        using ConstAccessor = HashMap::const_accessor;

        explicit LruWeightCache(
            uint32_t const max_weight,
            std::chrono::nanoseconds const lru_update_duration =
                std::chrono::milliseconds{200},
            bool const stamp_mode = false,
            bool (*const pinned)(Value const &) = nullptr)
            : max_weight_(max_weight)
            , weight_(0)
            , lru_{lru_update_duration.count()}
            , stamp_mode_{stamp_mode}
            , pinned_{pinned}
        {
        }

        LruWeightCache(LruWeightCache const &) = delete;
        LruWeightCache &operator=(LruWeightCache const &) = delete;

        bool find(ConstAccessor &acc, Key const &key)
        {
            if (!hmap_.find(acc, key)) {
                return false;
            }
            if (!stamp_mode_) {
                try_update_lru(&*acc);
            }
            return true;
        }

        // Stamp of the entry held by the accessor; 0 = unstamped.
        uint64_t stamp_of(ConstAccessor const &acc) const
        {
            return static_cast<uint64_t>(
                acc->second.lru_time_.load(std::memory_order_acquire));
        }

        // Negative entries only: promote at most once per block, reusing the
        // stamp field as the last-promotion block (never consensus-read).
        void promote_negative(ConstAccessor const &acc, uint64_t const block)
        {
            if (acc->second.lru_time_.load(std::memory_order_acquire) !=
                static_cast<int64_t>(block)) {
                lru_.update_lru_stamped(&*acc, static_cast<int64_t>(block));
            }
        }

        // Finalize path: set the consensus stamp of a resident entry and move
        // it to the front. Returns false when the entry is not resident (the
        // stamp is lost; the window still counts it, which only overcharges).
        bool set_stamp(Key const &key, uint64_t const stamp)
        {
            ConstAccessor acc;
            if (!hmap_.find(acc, key)) {
                return false;
            }
            lru_.update_lru_stamped(&*acc, static_cast<int64_t>(stamp));
            return true;
        }

        void set_pin_floor(uint64_t const floor)
        {
            pin_floor_.store(floor, std::memory_order_relaxed);
        }

        /// Insert `value` with `weight` under `key`. Overwrites if there is
        /// already a value under `key`.
        bool insert(Key const &key, Value const &value, uint32_t const weight)
        {
            int64_t delta_weight = weight;
            bool is_new_key = true;
            Accessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight}})) {
                ListNode *const node = &*acc;
                delta_weight -= node->second.cache_weight_;
                using std::swap;
                Value tmp = value;
                swap(node->second.value_, tmp);
                node->second.cache_weight_ = weight;
                if (!stamp_mode_) {
                    try_update_lru(node);
                }
                acc.release();
                is_new_key = false;
            }
            else {
                ListNode *const node = &*acc;
                acc.release();
                lru_.push_front(node);
            }
            adjust_by_delta_weight(delta_weight);
            return is_new_key;
        }

        // Not thread-safe with other cache operations.
        void clear()
        {
            hmap_.clear();
            lru_.clear();
            weight_.store(0, std::memory_order_release);
        }

        /// Like insert, but does not overwrite an existing value in the cache.
        /// Instead if a value already exists under `key` then it will
        /// overwrite the `value` argument with the existing value.
        bool try_insert(Key const &key, Value &value, uint32_t const weight)
        {
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight}})) {
                value = acc->second.value_;
                if (!stamp_mode_) {
                    try_update_lru(&*acc);
                }
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            lru_.push_front(node);
            adjust_by_delta_weight(weight);
            return true;
        }

        /// Like try_insert, but takes `value` by const reference and never
        /// mutates it or overwrites an existing entry. Returns true iff a new
        /// entry was inserted.
        bool try_insert_no_overwrite(
            Key const &key, Value const &value, uint32_t const weight)
        {
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight}})) {
                if (!stamp_mode_) {
                    try_update_lru(&*acc);
                }
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            lru_.push_front(node);
            adjust_by_delta_weight(weight);
            return true;
        }

        /// Get approximate total weight of the cached elements.
        uint64_t approx_weight() const
        {
            return static_cast<uint64_t>(
                weight_.load(std::memory_order_acquire));
        }

        /// Return the number of cached elements.
        size_t size() const noexcept
        {
            return hmap_.size();
        }

        // For testing: to check internal invariants. Not safe with
        // concurrent `insert` calls.
        bool unsafe_check_consistent()
        {
            return lru_.unsafe_check_consistent(hmap_, weight_.load());
        }

    private:
        void adjust_by_delta_weight(int64_t const delta_weight)
        {
            int64_t const pre_weight =
                weight_.fetch_add(delta_weight, std::memory_order_acq_rel);
            if (delta_weight + pre_weight > max_weight_) {
                int64_t evicted_weight = 0;
                int attempts = 0;
                while (evicted_weight < delta_weight && attempts++ < 256) {
                    ListNode const *target = lru_.evict();
                    if (MONAD_UNLIKELY(!target)) {
                        break;
                    }
                    // pinned victims (live value, stamp >= pin floor) go back
                    // to the front and the next victim is tried
                    if (stamp_mode_ && pinned_ != nullptr &&
                        pinned_(target->second.value_)) {
                        uint64_t const stamp =
                            static_cast<uint64_t>(target->second.lru_time_.load(
                                std::memory_order_acquire));
                        uint64_t const floor =
                            pin_floor_.load(std::memory_order_relaxed);
                        if (stamp != 0 && stamp >= floor) {
                            lru_.push_front_evicted(target);
                            continue;
                        }
                    }
                    int64_t const n = evict(target);
                    weight_.fetch_sub(n, std::memory_order_acq_rel);
                    evicted_weight += n;
                }
            }
        }

        void try_update_lru(ListNode const *const node)
        {
            if (node->second.check_lru_time(lru_.now())) {
                lru_.update_lru(node);
            }
        }

        uint32_t evict(ListNode const *const target)
        {
            Accessor acc;
            bool const found = hmap_.find(acc, target->first);
            MONAD_ASSERT(found);
            uint32_t const wt = acc->second.cache_weight_;
            hmap_.erase(acc);
            return wt;
        }

        /// HashMapValue
        struct HashMapValue
        {
            mutable ListNode const *prev_{};
            mutable ListNode const *next_{};
            mutable std::atomic<int64_t> lru_time_{0};
            Value value_;
            uint32_t cache_weight_;

            HashMapValue() = default;

            HashMapValue(Value const &value, uint32_t const weight)
                : value_{value}
                , cache_weight_{weight}
            {
            }

            // For insert into tbb hash map:
            HashMapValue(HashMapValue &&x) noexcept
                : prev_{x.prev_}
                , next_{x.next_}
                , lru_time_{x.lru_time_.load(std::memory_order_relaxed)}
                , value_{std::move(x.value_)}
                , cache_weight_{x.cache_weight_}
            {
            }

            bool is_in_list() const
            {
                return prev_ != nullptr;
            }

            void update_lru_time(int64_t const next_allowed) const
            {
                lru_time_.store(next_allowed, std::memory_order_release);
            }

            bool check_lru_time(int64_t const now) const
            {
                return now >= lru_time_.load(std::memory_order_acquire);
            }

            static int64_t wall_clock()
            {
                return std::chrono::duration_cast<std::chrono::nanoseconds>(
                           std::chrono::steady_clock::now().time_since_epoch())
                    .count();
            }
        }; /// HashMapValue

        /// LruList
        class LruList
        {
            ListNode base_;
            std::mutex mutex_;
            int64_t lru_update_period_;

        public:
            explicit LruList(int64_t const lru_update_period)
                : lru_update_period_{lru_update_period}
            {
                clear();
            }

            int64_t now() const
            {
                return ListNode::second_type::wall_clock();
            }

            int64_t next_allowed() const
            {
                return now() + lru_update_period_;
            }

            // Not thread-safe with other LruList operations.
            void clear()
            {
                base_.second.next_ = &base_;
                base_.second.prev_ = &base_;
            }

            void update_lru(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list()) {
                    delink(node);
                    front_link(node);
                    node->second.update_lru_time(next_allowed());
                } // else item is being evicted or inserted, don't update LRU
            }

            void push_front(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                front_link(node);
                node->second.update_lru_time(lru_update_period_);
            }

            // Stamp mode: move to the front and store the stamp verbatim in
            // the time field.
            void
            update_lru_stamped(ListNode const *const node, int64_t const stamp)
            {
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list()) {
                    delink(node);
                    front_link(node);
                    node->second.update_lru_time(stamp);
                }
            }

            // Re-link a node handed out by evict() (already delinked).
            void push_front_evicted(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                front_link(node);
            }

            ListNode const *evict()
            {
                std::unique_lock const l(mutex_);
                ListNode const *const target = base_.second.prev_;
                if (target == &base_) {
                    return nullptr;
                }
                delink(target);
                target->second.prev_ = nullptr;
                return target;
            }

            bool
            unsafe_check_consistent(HashMap const &hmap, int64_t const weight)
            {
                std::unordered_set<Key> keys;
                std::unique_lock l(mutex_);
                ListNode const *node = base_.second.next_;
                int64_t node_weight = 0;
                while (node != &base_) {
                    auto [_, inserted] = keys.insert(node->first);
                    if (!inserted) {
                        return false;
                    }
                    ConstAccessor acc;
                    bool found = hmap.find(acc, node->first);
                    MONAD_ASSERT(found);
                    node_weight += acc->second.cache_weight_;
                    node = node->second.next_;
                }
                return node_weight == weight;
            }

        private:
            void delink(ListNode const *const node)
            {
                ListNode const *const prev = node->second.prev_;
                ListNode const *const next = node->second.next_;
                prev->second.next_ = next;
                next->second.prev_ = prev;
            }

            void front_link(ListNode const *const node)
            {
                ListNode const *const head = base_.second.next_;
                node->second.prev_ = &base_;
                node->second.next_ = head;
                head->second.prev_ = node;
                base_.second.next_ = node;
            }
        }; /// LruList
    }; /// LruWeightCache
}
