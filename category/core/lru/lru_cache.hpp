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
#include <category/core/mem/batch_mem_pool.hpp>
#include <category/core/synchronization/spin_lock.hpp>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <string>

MONAD_NAMESPACE_BEGIN

template <
    class Key, class Value, class KeyHashCompare = tbb::tbb_hash_compare<Key>>
class LruCache
{
    /// TYPES
    struct ListNode;
    struct HashMapValue;
    struct LruList;
    using HashMap = tbb::concurrent_hash_map<Key, HashMapValue, KeyHashCompare>;
    using HashMapKeyValue = std::pair<Key, HashMapValue>;
    using Accessor = HashMap::accessor;
    using Mutex = SpinLock;
    using Pool = BatchMemPool<ListNode>;

    /// CONSTANTS
    static constexpr size_t SLACK = 16;

    /// DATA
    size_t max_size_;
    std::atomic<size_t> size_;
    LruList lru_;
    Mutex mutex_;
    HashMap hmap_;
    Pool pool_;
    // Stamp mode: the node time field holds the consensus stamp (last
    // qualifying access block) of live entries, written only by set_stamp at
    // finalize — find() never writes it. Negative entries reuse the field as
    // a local last-promotion block via promote_negative. Entries whose value
    // satisfies pinned_ and whose stamp >= the pin floor are never evicted.
    bool const stamp_mode_{false};
    bool (*const pinned_)(Value const &){nullptr};
    std::atomic<uint64_t> pin_floor_{0};

/// STATS MACROS
#ifdef MONAD_LRU_CACHE_STATS
    #define STATS_EVENT_EVICT() stats_.event_evict()
    #define STATS_EVENT_FIND_HIT() stats_.event_find_hit()
    #define STATS_EVENT_FIND_MISS() stats_.event_find_miss()
    #define STATS_EVENT_INSERT_FOUND() stats_.event_insert_found()
    #define STATS_EVENT_INSERT_NEW() stats_.event_insert_new()
    #define STATS_EVENT_UPDATE_LRU() stats_.event_update_lru()
#else
    #define STATS_EVENT_EVICT()
    #define STATS_EVENT_FIND_HIT()
    #define STATS_EVENT_FIND_MISS()
    #define STATS_EVENT_INSERT_FOUND()
    #define STATS_EVENT_INSERT_NEW()
    #define STATS_EVENT_UPDATE_LRU()
#endif

public:
    using ConstAccessor = HashMap::const_accessor;

    explicit LruCache(
        size_t const max_size, bool const stamp_mode = false,
        bool (*const pinned)(Value const &) = nullptr)
        : max_size_(max_size)
        , size_(0)
        , hmap_(max_size + SLACK)
        , pool_(max_size + SLACK, 1)
        , stamp_mode_(stamp_mode)
        , pinned_(pinned)
    {
    }

    LruCache(LruCache const &) = delete;
    LruCache &operator=(LruCache const &) = delete;

    ~LruCache()
    {
        clear();
    }

    bool find(ConstAccessor &acc, Key const &key)
    {
        if (!hmap_.find(acc, key)) {
            STATS_EVENT_FIND_MISS();
            return false;
        }
        STATS_EVENT_FIND_HIT();
        if (!stamp_mode_) {
            ListNode *const node = acc->second.node_;
            try_update_lru(node);
        }
        return true;
    }

    // Stamp of the entry held by the accessor; 0 = unstamped.
    uint64_t stamp_of(ConstAccessor const &acc) const
    {
        return static_cast<uint64_t>(
            acc->second.node_->lru_time_.load(std::memory_order_acquire));
    }

    // Negative entries only: promote at most once per block, reusing the
    // stamp field as the last-promotion block (never consensus-read).
    void promote_negative(ConstAccessor const &acc, uint64_t const block)
    {
        ListNode *const node = acc->second.node_;
        if (node->check_lru_time(static_cast<int64_t>(block), 1)) {
            std::unique_lock const l(mutex_);
            STATS_EVENT_UPDATE_LRU();
            lru_.update_lru(node, static_cast<int64_t>(block));
        }
    }

    // Finalize path: set the consensus stamp of a resident entry and move it
    // to the front. Returns false when the entry is not resident (the stamp
    // is lost; the window still counts it, which only overcharges).
    bool set_stamp(Key const &key, uint64_t const stamp)
    {
        ConstAccessor acc;
        if (!hmap_.find(acc, key)) {
            return false;
        }
        ListNode *const node = acc->second.node_;
        std::unique_lock const l(mutex_);
        lru_.update_lru(node, static_cast<int64_t>(stamp));
        return true;
    }

    void set_pin_floor(uint64_t const floor)
    {
        pin_floor_.store(floor, std::memory_order_relaxed);
    }

    bool insert(Key const &key, Value const &value)
    {
        Accessor acc;
        HashMapKeyValue const hmkv(key, HashMapValue(value, nullptr));
        if (!hmap_.insert(acc, hmkv)) {
            STATS_EVENT_INSERT_FOUND();
            acc->second.value_ = value;
            if (!stamp_mode_) {
                ListNode *const node = acc->second.node_;
                try_update_lru(node);
            }
            return false;
        }
        ListNode *const node = pool_.new_obj(key);
        acc->second.node_ = node;
        acc.release();
        finish_insert(node);
        return true;
    }

    void clear() // Not thread-safe with other cache operations
    {
        hmap_.clear();
        lru_.clear(pool_);
        size_.store(0, std::memory_order_release);
    }

    size_t size() const
    {
        return size_.load(std::memory_order_acquire);
    }

private:
    void try_update_lru(ListNode *node)
    {
        int64_t const t = ListNode::wall_clock();
        if (node->check_lru_time(t, ListNode::LRU_UPDATE_PERIOD)) {
            std::unique_lock const l(mutex_);
            STATS_EVENT_UPDATE_LRU();
            lru_.update_lru(node, t);
        }
    }

    void finish_insert(ListNode *node)
    {
        size_t sz = size();
        bool const evicted = (sz >= max_size_) && evict();
        {
            std::unique_lock const l(mutex_);
            STATS_EVENT_INSERT_NEW();
            lru_.push_front(node);
        }
        if (!evicted) {
            sz = 1 + size_.fetch_add(1, std::memory_order_acq_rel);
        }
        if (sz > max_size_) {
            if (size_.compare_exchange_strong(
                    sz,
                    sz - 1,
                    std::memory_order_acq_rel,
                    std::memory_order_relaxed)) {
                if (!evict()) {
                    size_.fetch_add(1, std::memory_order_release);
                }
            }
        }
    }

    bool evict()
    {
        // pinned victims (live value, stamp >= pin floor) go back to the
        // front and the next victim is tried; the retry cap keeps a fully
        // pinned tail from spinning (the cache then grows transiently)
        for (int attempt = 0; attempt < 64; ++attempt) {
            ListNode *target;
            {
                std::unique_lock const l(mutex_);
                STATS_EVENT_EVICT();
                target = lru_.evict();
            }
            if (!target) {
                return false;
            }
            Accessor acc;
            bool const found = hmap_.find(acc, target->key_);
            MONAD_ASSERT(found);
            if (stamp_mode_ && pinned_ != nullptr &&
                pinned_(acc->second.value_)) {
                uint64_t const stamp = static_cast<uint64_t>(
                    target->lru_time_.load(std::memory_order_acquire));
                uint64_t const floor =
                    pin_floor_.load(std::memory_order_relaxed);
                if (stamp != 0 && stamp >= floor) {
                    acc.release();
                    std::unique_lock const l(mutex_);
                    lru_.push_front(target);
                    continue;
                }
            }
            hmap_.erase(acc);
            pool_.delete_obj(target);
            return true;
        }
        return false;
    }

    /// ListNode
    struct ListNode
    {
        static constexpr int64_t ONE_SECOND = 1'000'000'000;
        static constexpr int64_t LRU_UPDATE_PERIOD = 1 * ONE_SECOND;

        ListNode *prev_{nullptr};
        ListNode *next_{nullptr};
        Key key_;
        std::atomic<int64_t> lru_time_{0};

        ListNode() = default;

        explicit ListNode(Key const &key)
            : key_(key)
        {
        }

        bool is_in_list() const
        {
            return prev_ != nullptr;
        }

        void update_lru_time(int64_t const now)
        {
            lru_time_.store(now, std::memory_order_release);
        }

        bool check_lru_time(int64_t const now, int64_t const period) const
        {
            return (now - lru_time_.load(std::memory_order_acquire)) >= period;
        }

        static int64_t wall_clock()
        {
            return (int64_t)
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                       std::chrono::steady_clock::now().time_since_epoch())
                    .count();
        }
    }; /// ListNode

    /// LruList
    struct LruList
    {
        ListNode head_;
        ListNode tail_;

        LruList()
        {
            head_.next_ = &tail_;
            tail_.prev_ = &head_;
        }

        void update_lru(ListNode *node, int64_t const now)
        {
            if (node->is_in_list()) {
                delink(node);
                push_front(node);
                node->update_lru_time(now);
            } // else item is being evicted, don't update LRU
        }

        void delink(ListNode *node)
        {
            ListNode *const prev = node->prev_;
            ListNode *const next = node->next_;
            prev->next_ = next;
            next->prev_ = prev;
            node->prev_ = nullptr;
        }

        void push_front(ListNode *node)
        {
            ListNode *const head = head_.next_;
            node->prev_ = &head_;
            node->next_ = head;
            head->prev_ = node;
            head_.next_ = node;
        }

        void clear(Pool &pool)
        {
            ListNode *node = head_.next_;
            ListNode *next;
            while (node != &tail_) {
                next = node->next_;
                pool.delete_obj(node);
                node = next;
            }
            head_.next_ = &tail_;
            tail_.prev_ = &head_;
        }

        ListNode *evict()
        {
            ListNode *const target = tail_.prev_;
            if (target == &head_) {
                return nullptr;
            }
            delink(target);
            return target;
        }
    }; /// LruList

    /// HashMapValue
    struct HashMapValue
    {
        Value value_;
        ListNode *node_;

        HashMapValue() = default;

        HashMapValue(Value const &value, ListNode *const node)
            : value_(value)
            , node_(node)
        {
        }
    }; /// HashMapValue

/// STATS
#undef STATS_EVENT_EVICT
#undef STATS_EVENT_FIND_HIT
#undef STATS_EVENT_FIND_MISS
#undef STATS_EVENT_INSERT_FOUND
#undef STATS_EVENT_INSERT_NEW
#undef STATS_EVENT_UPDATE_LRU

public:
    std::string print_stats()
    {
        std::string str =
            std::format("{:8}", size_.load(std::memory_order_acquire));
#ifdef MONAD_LRU_CACHE_STATS
        str += " / " + stats_.print_stats();
#endif
        return str;
    }

private:
#ifdef MONAD_LRU_CACHE_STATS
    /// CacheStats
    struct CacheStats
    {
        std::atomic<uint64_t> n_find_hit_{0};
        std::atomic<uint64_t> n_find_miss_{0};
        std::atomic<uint64_t> n_insert_found_{0};
        uint64_t n_insert_new_{0};
        uint64_t n_evict_{0};
        uint64_t n_update_lru_{0};

        void event_find_hit()
        {
            n_find_hit_.fetch_add(1, std::memory_order_release);
        }

        void event_find_miss()
        {
            n_find_miss_.fetch_add(1, std::memory_order_release);
        }

        void event_insert_found()
        {
            n_insert_found_.fetch_add(1, std::memory_order_release);
        }

        void event_insert_new()
        {
            ++n_insert_new_;
        }

        void event_evict()
        {
            ++n_evict_;
        }

        void event_update_lru()
        {
            ++n_update_lru_;
        }

        void clear_stats()
        {
            // Not called concurrently with cache operations.
            n_find_hit_.store(0, std::memory_order_release);
            n_find_miss_.store(0, std::memory_order_release);
            n_insert_found_.store(0, std::memory_order_release);
            n_insert_new_ = 0;
            n_evict_ = 0;
            n_update_lru_ = 0;
        }

        std::string print_stats()
        {
            std::string str = std::format(
                "{:6} {:6} - {:6} {:6} - {:6} - {:6}",
                n_find_hit_.load(std::memory_order_acquire),
                n_find_miss_.load(std::memory_order_acquire),
                n_insert_found_.load(std::memory_order_acquire),
                n_insert_new_,
                n_evict_,
                n_update_lru_);
            clear_stats();
            return str;
        }
    }; /// CacheStats

    CacheStats stats_;
#endif /// MONAD_LRU_CACHE_STATS

}; /// LruCache

MONAD_NAMESPACE_END
