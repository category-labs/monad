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
#include <optional>
#include <string>
#include <utility>

#include <unordered_set>

namespace monad::vm::utils
{
    // LRU Cache in which elements can have different weights. It is based
    // on the LruCache in monad.
    //
    // The list has two heads: [head1: protected ...][head2: unprotected ...
    // tail]. Inserts and read promotions go to head2, and eviction by weight
    // pops from the tail, so it only ever removes unprotected elements.
    // Protected elements count towards the weight but are never promoted or
    // evicted by weight: the owner moves them to head1 with protect_front()
    // and demotes the one just before head2 with demote_oldest_protected().
    // Protected elements are in the order the owner protected them, newest
    // at head1; the owner keeps any ordering key, such as a stamp, in the
    // value. lru_time_ is only a wall-clock rate limit on promoting
    // unprotected elements and plays no part in the protected order.
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
        uint64_t max_weight_;
        std::atomic<int64_t> weight_;
        LruList lru_;
        HashMap hmap_;

    public:
        using ConstAccessor = HashMap::const_accessor;

        explicit LruWeightCache(
            uint64_t const max_weight,
            std::chrono::nanoseconds const lru_update_duration =
                std::chrono::milliseconds{200})
            : max_weight_(max_weight)
            , weight_(0)
            , lru_{lru_update_duration.count()}
        {
        }

        LruWeightCache(LruWeightCache const &) = delete;
        LruWeightCache &operator=(LruWeightCache const &) = delete;

        bool find(ConstAccessor &acc, Key const &key)
        {
            if (!hmap_.find(acc, key)) {
                return false;
            }
            try_update_lru(&*acc);
            return true;
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
                try_update_lru(node);
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
                try_update_lru(&*acc);
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
                try_update_lru(&*acc);
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            lru_.push_front(node);
            adjust_by_delta_weight(weight);
            return true;
        }

        /// Move the element under `key` to head1, making it the newest
        /// protected element. Returns false if `key` is not cached. Not
        /// thread-safe with other protect/demote calls.
        bool protect_front(Key const &key)
        {
            ConstAccessor acc;
            if (!hmap_.find(acc, key)) {
                return false;
            }
            lru_.protect_front(&*acc);
            return true;
        }

        /// The key of the oldest protected element, the one just before
        /// head2, if any.
        std::optional<Key> oldest_protected()
        {
            ListNode const *const node = lru_.oldest_protected();
            if (!node) {
                return std::nullopt;
            }
            return node->first;
        }

        /// Make the oldest protected element the newest unprotected one by
        /// moving head2 back past it. The element stays cached.
        void demote_oldest_protected()
        {
            lru_.demote_oldest_protected();
        }

        // Remove every unprotected element, keeping the protected ones. Not
        // thread-safe with other cache operations.
        void clear_unprotected()
        {
            while (ListNode const *const target = lru_.evict()) {
                weight_.fetch_sub(evict(target), std::memory_order_acq_rel);
            }
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
            if (delta_weight + pre_weight > static_cast<int64_t>(max_weight_)) {
                int64_t evicted_weight = 0;
                while (evicted_weight < delta_weight) {
                    ListNode const *target = lru_.evict();
                    if (MONAD_UNLIKELY(!target)) {
                        // The weight budget must cover every protected
                        // element, so eviction never needs to reach them.
                        MONAD_ASSERT(
                            !lru_.has_protected(),
                            "weight eviction reached protected elements");
                        break;
                    }
                    int64_t const n = evict(target);
                    weight_.fetch_sub(n, std::memory_order_acq_rel);
                    evicted_weight += n;
                }
            }
        }

        void try_update_lru(ListNode const *const node)
        {
            if (!node->second.protected_ && node->second.check_lru_time()) {
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
            mutable bool protected_{false};
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
                , protected_{x.protected_}
                , value_{std::move(x.value_)}
                , cache_weight_{x.cache_weight_}
            {
            }

            bool is_in_list() const
            {
                return prev_ != nullptr;
            }

            void update_lru_time(int64_t const update_period) const
            {
                lru_time_.store(
                    cur_time() + update_period, std::memory_order_release);
            }

            bool check_lru_time() const
            {
                return cur_time() >= lru_time_.load(std::memory_order_acquire);
            }

            static int64_t cur_time()
            {
                return std::chrono::duration_cast<std::chrono::nanoseconds>(
                           std::chrono::steady_clock::now().time_since_epoch())
                    .count();
            }
        }; /// HashMapValue

        /// LruList
        // base_ is head1 and base2_ is head2: base_ -> protected nodes ->
        // base2_ -> unprotected nodes -> base_, with the tail at base_.prev_.
        class LruList
        {
            ListNode base_;
            ListNode base2_;
            std::mutex mutex_;
            int64_t lru_update_period_;

        public:
            explicit LruList(int64_t const lru_update_period)
                : lru_update_period_{lru_update_period}
            {
                clear();
            }

            // Not thread-safe with other LruList operations.
            void clear()
            {
                base_.second.next_ = &base2_;
                base_.second.prev_ = &base2_;
                base2_.second.next_ = &base_;
                base2_.second.prev_ = &base_;
            }

            void update_lru(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list() && !node->second.protected_) {
                    delink(node);
                    link_after(&base2_, node);
                    node->second.update_lru_time(lru_update_period_);
                } // else item is protected, or being evicted or inserted
            }

            void push_front(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                link_after(&base2_, node);
                node->second.update_lru_time(lru_update_period_);
            }

            // Pop the tail if it is unprotected.
            ListNode const *evict()
            {
                std::unique_lock const l(mutex_);
                ListNode const *const target = base_.second.prev_;
                if (target == &base2_) {
                    return nullptr;
                }
                delink(target);
                target->second.prev_ = nullptr;
                return target;
            }

            void protect_front(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                MONAD_ASSERT(node->second.is_in_list());
                delink(node);
                link_after(&base_, node);
                node->second.protected_ = true;
            }

            ListNode const *oldest_protected()
            {
                std::unique_lock const l(mutex_);
                ListNode const *const node = base2_.second.prev_;
                return node == &base_ ? nullptr : node;
            }

            void demote_oldest_protected()
            {
                std::unique_lock const l(mutex_);
                ListNode const *const node = base2_.second.prev_;
                MONAD_ASSERT(node != &base_);
                delink(&base2_);
                link_after(node->second.prev_, &base2_);
                node->second.protected_ = false;
                // Now the newest unprotected node, as after push_front.
                node->second.update_lru_time(lru_update_period_);
            }

            bool has_protected()
            {
                std::unique_lock const l(mutex_);
                return base_.second.next_ != &base2_;
            }

            bool
            unsafe_check_consistent(HashMap const &hmap, int64_t const weight)
            {
                std::unordered_set<Key> keys;
                std::unique_lock l(mutex_);
                ListNode const *node = base_.second.next_;
                int64_t node_weight = 0;
                bool expect_protected = true;
                while (node != &base_) {
                    if (node == &base2_) {
                        expect_protected = false;
                        node = node->second.next_;
                        continue;
                    }
                    if (node->second.protected_ != expect_protected) {
                        return false;
                    }
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
                return !expect_protected && node_weight == weight;
            }

        private:
            void delink(ListNode const *const node)
            {
                ListNode const *const prev = node->second.prev_;
                ListNode const *const next = node->second.next_;
                prev->second.next_ = next;
                next->second.prev_ = prev;
            }

            void
            link_after(ListNode const *const anchor, ListNode const *const node)
            {
                ListNode const *const next = anchor->second.next_;
                node->second.prev_ = anchor;
                node->second.next_ = next;
                next->second.prev_ = node;
                anchor->second.next_ = node;
            }
        }; /// LruList
    }; /// LruWeightCache
}
