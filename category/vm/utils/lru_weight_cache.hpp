#pragma once

#include <category/vm/core/assert.h>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <string>

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

    public:
        using ConstAccessor = HashMap::const_accessor;

        explicit LruWeightCache(
            uint32_t max_weight, std::chrono::nanoseconds lru_update_duration =
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
        bool insert(Key const &key, Value const &value, uint32_t weight)
        {
            int64_t delta_weight = weight;
            bool is_new_key = true;
            Accessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight}})) {
                ListNode *const node = &*acc;
                delta_weight -= node->second.cache_weight_;
                node->second.value_ = value;
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

        /// Like insert, but does not overwrite an existing value in the cache.
        /// Instead if a value already exists under `key` then it will
        /// overwrite the `value` argument with the existing value.
        bool try_insert(Key const &key, Value &value, uint32_t weight)
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

        /// Get approximate total weight of the cached elements.
        uint64_t approx_weight()
        {
            return static_cast<uint64_t>(
                weight_.load(std::memory_order_acquire));
        }

        // For testing: to check internal invariants. Not safe with
        // concurrent `insert` calls.
        bool unsafe_check_consistent()
        {
            return lru_.unsafe_check_consistent(hmap_, weight_.load());
        }

    private:
        void adjust_by_delta_weight(int64_t delta_weight)
        {
            int64_t const pre_weight =
                weight_.fetch_add(delta_weight, std::memory_order_acq_rel);
            if (delta_weight + pre_weight > max_weight_) {
                int64_t evicted_weight = 0;
                while (evicted_weight < delta_weight) {
                    ListNode const *target = lru_.evict();
                    if (MONAD_VM_UNLIKELY(!target)) {
                        break;
                    }
                    int64_t const n = evict(target);
                    weight_.fetch_sub(n, std::memory_order_acq_rel);
                    evicted_weight += n;
                }
            }
        }

        void try_update_lru(ListNode const *node)
        {
            if (node->second.check_lru_time()) {
                lru_.update_lru(node);
            }
        }

        uint32_t evict(ListNode const *target)
        {
            Accessor acc;
            bool const found = hmap_.find(acc, target->first);
            MONAD_VM_ASSERT(found);
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

            HashMapValue(Value const &value, uint32_t weight)
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

            void update_lru_time(int64_t update_period) const
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
        class LruList
        {
            ListNode base_;
            std::mutex mutex_;
            int64_t lru_update_period_;

        public:
            explicit LruList(int64_t lru_update_period)
                : lru_update_period_{lru_update_period}
            {
                base_.second.next_ = &base_;
                base_.second.prev_ = &base_;
            }

            void update_lru(ListNode const *node)
            {
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list()) {
                    delink(node);
                    front_link(node);
                    node->second.update_lru_time(lru_update_period_);
                } // else item is being evicted or inserted, don't update LRU
            }

            void push_front(ListNode const *node)
            {
                std::unique_lock const l(mutex_);
                front_link(node);
                node->second.update_lru_time(lru_update_period_);
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

            bool unsafe_check_consistent(HashMap const &hmap, int64_t weight)
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
                    MONAD_VM_ASSERT(found);
                    node_weight += acc->second.cache_weight_;
                    node = node->second.next_;
                }
                return node_weight == weight;
            }

        private:
            void delink(ListNode const *node)
            {
                ListNode const *const prev = node->second.prev_;
                ListNode const *const next = node->second.next_;
                prev->second.next_ = next;
                next->second.prev_ = prev;
            }

            void front_link(ListNode const *node)
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
