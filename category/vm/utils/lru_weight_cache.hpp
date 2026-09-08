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
        // Stamp mode: the entry time field holds the consensus stamp,
        // written only by set_stamp at finalize — find() and insert() never
        // promote or write it, so list order is stamp order and the tail is
        // always the oldest-stamped (or unstamped) entry. Eviction of a warm
        // entry (stamp >= the evict floor E) is impossible by construction
        // while budget + in-flight inserts < capacity; eviction asserts it.
        bool const stamp_mode_{false};
        std::atomic<uint64_t> evict_floor_{0};
        // negative entries sit on their own count-budgeted list; the shared
        // weight budget covers live entries only
        size_t const negative_max_{0};
        std::atomic<size_t> negative_size_{0};
        LruList negative_lru_;

    public:
        using ConstAccessor = HashMap::const_accessor;

        explicit LruWeightCache(
            uint32_t const max_weight,
            std::chrono::nanoseconds const lru_update_duration =
                std::chrono::milliseconds{200},
            bool const stamp_mode = false, size_t const negative_max = 0)
            : max_weight_(max_weight)
            , weight_(0)
            , lru_{lru_update_duration.count()}
            , stamp_mode_{stamp_mode}
            , negative_max_{negative_max}
            , negative_lru_{lru_update_duration.count()}
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
                try_update_lru(lru_, &*acc);
            }
            else if (acc->second.negative_) {
                try_update_lru(negative_lru_, &*acc);
            }
            return true;
        }

        bool is_negative(ConstAccessor const &acc) const
        {
            return acc->second.negative_;
        }

        // Consensus stamp of a live entry; 0 = unstamped (and for negative
        // entries, whose time field is local recency).
        uint64_t stamp_of(ConstAccessor const &acc) const
        {
            if (acc->second.negative_) {
                return 0;
            }
            return static_cast<uint64_t>(
                acc->second.lru_time_.load(std::memory_order_acquire));
        }

        // Finalize path: set the consensus stamp of a resident entry and move
        // it to the front. Returns false when the entry is not resident (the
        // stamp is lost; the window still counts it, which only overcharges).
        bool set_stamp(Key const &key, uint64_t const stamp)
        {
            ConstAccessor acc;
            if (!hmap_.find(acc, key) || acc->second.negative_) {
                return false;
            }
            lru_.update_lru_stamped(&*acc, static_cast<int64_t>(stamp));
            return true;
        }

        void set_evict_floor(uint64_t const floor)
        {
            evict_floor_.store(floor, std::memory_order_relaxed);
        }

        /// Insert `value` with `weight` under `key`. Overwrites if there is
        /// already a value under `key`. In stamp mode `negative` selects the
        /// list; a changed flag flips the entry in place.
        bool insert(
            Key const &key, Value const &value, uint32_t const weight,
            bool const negative = false)
        {
            bool const neg = stamp_mode_ && negative;
            Accessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, neg}})) {
                ListNode *const node = &*acc;
                bool const was_negative = node->second.negative_;
                int64_t delta_weight = neg ? 0 : weight;
                if (!was_negative) {
                    delta_weight -= node->second.cache_weight_;
                }
                using std::swap;
                Value tmp = value;
                swap(node->second.value_, tmp);
                node->second.cache_weight_ = weight;
                if (!stamp_mode_) {
                    try_update_lru(lru_, node);
                }
                else if (was_negative != neg) {
                    transition(node, neg);
                }
                acc.release();
                if (delta_weight != 0) {
                    adjust_by_delta_weight(delta_weight);
                }
                return false;
            }
            ListNode *const node = &*acc;
            acc.release();
            if (neg) {
                negative_lru_.push_front(node);
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                lru_.push_front(node);
                if (stamp_mode_) {
                    node->second.update_lru_time(0); // unstamped
                }
                adjust_by_delta_weight(weight);
            }
            return true;
        }

        // Not thread-safe with other cache operations.
        void clear()
        {
            hmap_.clear();
            lru_.clear();
            negative_lru_.clear();
            weight_.store(0, std::memory_order_release);
            negative_size_.store(0, std::memory_order_release);
        }

        /// Like insert, but does not overwrite an existing value in the cache.
        /// Instead if a value already exists under `key` then it will
        /// overwrite the `value` argument with the existing value.
        bool try_insert(Key const &key, Value &value, uint32_t const weight)
        {
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, false}})) {
                value = acc->second.value_;
                if (!stamp_mode_) {
                    try_update_lru(lru_, &*acc);
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
            Key const &key, Value const &value, uint32_t const weight,
            bool const negative = false)
        {
            bool const neg = stamp_mode_ && negative;
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, neg}})) {
                if (!stamp_mode_) {
                    try_update_lru(lru_, &*acc);
                }
                else if (acc->second.negative_) {
                    try_update_lru(negative_lru_, &*acc);
                }
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            if (neg) {
                negative_lru_.push_front(node);
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                lru_.push_front(node);
                if (stamp_mode_) {
                    node->second.update_lru_time(0); // unstamped
                }
                adjust_by_delta_weight(weight);
            }
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
                while (evicted_weight < delta_weight) {
                    ListNode const *target = lru_.evict();
                    if (MONAD_UNLIKELY(!target)) {
                        break;
                    }
                    if (stamp_mode_) {
                        // the tail is the oldest-stamped entry, so a warm
                        // victim means the warm set outgrew the physical
                        // capacity — a consensus bug, not a perf bug
                        uint64_t const stamp =
                            static_cast<uint64_t>(target->second.lru_time_.load(
                                std::memory_order_acquire));
                        MONAD_ASSERT(
                            stamp == 0 ||
                            stamp <
                                evict_floor_.load(std::memory_order_relaxed));
                    }
                    int64_t const n = evict(target);
                    weight_.fetch_sub(n, std::memory_order_acq_rel);
                    evicted_weight += n;
                }
            }
        }

        void try_update_lru(LruList &list, ListNode const *const node)
        {
            if (node->second.check_lru_time(list.now())) {
                list.update_lru(node);
            }
        }

        // Flip an entry between the live and negative lists in place
        // (finalize path: the value was created or deleted). Weight and count
        // budgets are adjusted by the caller via delta_weight/trim.
        void transition(ListNode *const node, bool const negative)
        {
            if (!(negative ? negative_lru_ : lru_)
                     .relink_from(
                         negative ? lru_ : negative_lru_, node, negative)) {
                return; // being evicted concurrently
            }
            if (negative) {
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }

        void trim_negative(size_t const size)
        {
            if (size > negative_max_ && evict_negative()) {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }

        bool evict_negative()
        {
            ListNode const *const target = negative_lru_.evict();
            if (!target) {
                return false;
            }
            evict(target);
            return true;
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
            mutable bool negative_{false};

            HashMapValue() = default;

            HashMapValue(
                Value const &value, uint32_t const weight,
                bool const negative = false)
                : value_{value}
                , cache_weight_{weight}
                , negative_{negative}
            {
            }

            // For insert into tbb hash map:
            HashMapValue(HashMapValue &&x) noexcept
                : prev_{x.prev_}
                , next_{x.next_}
                , lru_time_{x.lru_time_.load(std::memory_order_relaxed)}
                , value_{std::move(x.value_)}
                , cache_weight_{x.cache_weight_}
                , negative_{x.negative_}
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

            // Move a node from `src` onto this list's front, updating the
            // negative flag and resetting the time field (fresh recency for
            // negatives, unstamped for live). False when the node is not in
            // any list (a concurrent eviction already claimed it).
            bool relink_from(
                LruList &src, ListNode const *const node, bool const negative)
            {
                std::scoped_lock const l(mutex_, src.mutex_);
                if (!node->second.is_in_list()) {
                    return false;
                }
                src.delink(node);
                node->second.negative_ = negative;
                node->second.update_lru_time(
                    negative ? ListNode::second_type::wall_clock() : 0);
                front_link(node);
                return true;
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
