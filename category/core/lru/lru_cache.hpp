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

// Default mode: a plain LRU with wall-clock rate-limited promotion on find.
//
// Stamp mode (multi-block cache): one hash map, two eviction lists. An
// entry has a value flag (negative_: the key holds nothing) and a region
// flag (stamped_: it carries a consensus stamp in the time field, written
// only by set_stamp at finalize). Stamped entries — with or without a value
// — sit at the head of the live list in stamp order and never move on a
// read; unstamped live entries sit behind a fixed boundary sentinel and
// unstamped negative entries on the negative list, both plain wall-clock
// LRUs (a read promotes, rate limited), so an entry a block reads survives
// the block's own inserts until finalize stamps it. Eviction takes the live
// tail, so unstamped entries go first and the stamped region — kept equal
// to the cached set by demote_expired — is never reached while the cached
// set fits the capacity; evict() asserts it. A value transition
// (create/delete at finalize) never moves a stamped entry — the stamp
// survives until clear_stamp (a death record) — and flips an unstamped
// entry between the negative list and the unstamped region in place: one
// map, no cross-cache invalidation.
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
    bool const stamp_mode_{false};
    size_t const negative_max_{0};
    std::atomic<size_t> negative_size_{0};
    LruList negative_lru_;
    std::atomic<uint64_t> evict_floor_{0};
    // stamp mode: boundary between the stamped region (ahead) and the
    // unstamped region (behind) of the live list; never evicted
    ListNode boundary_;
    // stamped entries without a value (measurement aid)
    std::atomic<size_t> stamped_negative_{0};

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
        size_t const negative_max = 0)
        : max_size_(max_size)
        , size_(0)
        , hmap_(max_size + negative_max + SLACK)
        , pool_(max_size + negative_max + SLACK, 1)
        , stamp_mode_(stamp_mode)
        , negative_max_(negative_max)
    {
        if (stamp_mode_) {
            lru_.push_front(&boundary_);
        }
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
        ListNode *const node = acc->second.node_;
        if (!stamp_mode_) {
            try_update_lru(lru_, node);
        }
        else if (!node->stamped_) {
            // the unstamped regions are plain LRUs: a read promotes (rate
            // limited), so an entry read in this block cannot be the victim
            // of the block's own inserts before finalize stamps it. Stamped
            // entries never move on a read: their order is the stamp order.
            try_update_unstamped(node);
        }
        return true;
    }

    bool is_negative(ConstAccessor const &acc) const
    {
        return acc->second.node_->negative_;
    }

    // Consensus stamp of an entry; 0 = unstamped.
    uint64_t stamp_of(ConstAccessor const &acc) const
    {
        ListNode const *const node = acc->second.node_;
        if (!node->stamped_) {
            return 0;
        }
        return static_cast<uint64_t>(
            node->lru_time_.load(std::memory_order_acquire));
    }

    size_t stamped_negative_count() const
    {
        return stamped_negative_.load(std::memory_order_relaxed);
    }

    // Finalize path: set the consensus stamp of a resident entry (with or
    // without a value) and move it to the front of the stamped region.
    // Returns false when the entry is not resident.
    bool set_stamp(Key const &key, uint64_t const stamp)
    {
        ConstAccessor acc;
        if (!hmap_.find(acc, key)) {
            return false;
        }
        ListNode *const node = acc->second.node_;
        bool from_negative_list = false;
        {
            std::unique_lock const l(mutex_);
            if (!node->is_in_list()) {
                return false; // being evicted concurrently
            }
            if (node->stamped_) {
                lru_.update_lru(node, static_cast<int64_t>(stamp));
                return true;
            }
            from_negative_list = node->negative_;
            (from_negative_list ? negative_lru_ : lru_).delink(node);
            node->stamped_ = true;
            lru_.push_front(node);
            node->update_lru_time(static_cast<int64_t>(stamp));
        }
        if (from_negative_list) {
            // the entry now occupies live capacity
            stamped_negative_.fetch_add(1, std::memory_order_relaxed);
            negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            size_t const sz = 1 + size_.fetch_add(1, std::memory_order_acq_rel);
            if (sz > max_size_ && evict()) {
                size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }
        return true;
    }

    // Death record (finalize / bootstrap): forget the stamp of a resident
    // entry. A live entry moves to the front of the unstamped region, an
    // empty one to the negative list — where an unstamped entry of that
    // value would be.
    bool clear_stamp(Key const &key)
    {
        ConstAccessor acc;
        if (!hmap_.find(acc, key)) {
            return false;
        }
        ListNode *const node = acc->second.node_;
        bool to_negative_list = false;
        {
            std::unique_lock const l(mutex_);
            if (!node->is_in_list() || !node->stamped_) {
                return node->is_in_list();
            }
            lru_.delink(node);
            node->stamped_ = false;
            to_negative_list = node->negative_;
            if (to_negative_list) {
                negative_lru_.push_front(node);
                node->update_lru_time(ListNode::wall_clock());
            }
            else {
                lru_.insert_after(&boundary_, node);
                node->update_lru_time(0);
            }
        }
        if (to_negative_list) {
            stamped_negative_.fetch_sub(1, std::memory_order_relaxed);
            size_.fetch_sub(1, std::memory_order_acq_rel);
            size_t const sz =
                1 + negative_size_.fetch_add(1, std::memory_order_acq_rel);
            if (sz > negative_max_ && evict_negative()) {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }
        return true;
    }

    void set_evict_floor(uint64_t const floor)
    {
        evict_floor_.store(floor, std::memory_order_relaxed);
    }

    // Finalize path, after the floor advanced: entries whose stamp fell
    // below it are no longer cached and leave the stamped region — a live
    // one to the front of the unstamped region (it was touched within the
    // last window, more recently than most entries there), an empty one to
    // the negative list — so the stamped region is exactly the cached set
    // and expired stamps cannot crowd out fresh inserts. The stamped region
    // is in stamp order, so the expired entries are exactly its tail.
    void demote_expired(uint64_t const floor)
    {
        size_t to_negative = 0;
        {
            std::unique_lock const l(mutex_);
            while (true) {
                ListNode *const node = boundary_.prev_;
                if (node == &lru_.head_ || !node->stamped_ ||
                    static_cast<uint64_t>(node->lru_time_.load(
                        std::memory_order_acquire)) >= floor) {
                    break;
                }
                lru_.delink(node);
                node->stamped_ = false;
                if (node->negative_) {
                    negative_lru_.push_front(node);
                    node->update_lru_time(ListNode::wall_clock());
                    ++to_negative;
                }
                else {
                    lru_.insert_after(&boundary_, node);
                    node->update_lru_time(ListNode::wall_clock());
                }
            }
        }
        if (to_negative != 0) {
            stamped_negative_.fetch_sub(to_negative, std::memory_order_relaxed);
            size_.fetch_sub(to_negative, std::memory_order_acq_rel);
            size_t const sz = negative_size_.fetch_add(
                                  to_negative, std::memory_order_acq_rel) +
                              to_negative;
            for (size_t i = negative_max_; i < sz; ++i) {
                if (!evict_negative()) {
                    break;
                }
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }
    }

    bool insert(Key const &key, Value const &value, bool const negative = false)
    {
        Accessor acc;
        HashMapKeyValue const hmkv(key, HashMapValue(value, nullptr));
        if (!hmap_.insert(acc, hmkv)) {
            STATS_EVENT_INSERT_FOUND();
            acc->second.value_ = value;
            ListNode *const node = acc->second.node_;
            if (!stamp_mode_) {
                try_update_lru(lru_, node);
            }
            else if (node->negative_ != negative) {
                transition(node, negative);
            }
            return false;
        }
        ListNode *const node = pool_.new_obj(key);
        node->negative_ = stamp_mode_ && negative;
        acc->second.node_ = node;
        acc.release();
        finish_insert(node);
        return true;
    }

    void clear() // Not thread-safe with other cache operations
    {
        hmap_.clear();
        if (stamp_mode_) {
            lru_.delink(&boundary_);
        }
        lru_.clear(pool_);
        if (stamp_mode_) {
            lru_.push_front(&boundary_);
        }
        negative_lru_.clear(pool_);
        size_.store(0, std::memory_order_release);
        negative_size_.store(0, std::memory_order_release);
    }

    size_t size() const
    {
        return size_.load(std::memory_order_acquire);
    }

private:
    void try_update_lru(LruList &list, ListNode *node)
    {
        int64_t const t = ListNode::wall_clock();
        if (node->check_lru_time(t, ListNode::LRU_UPDATE_PERIOD)) {
            std::unique_lock const l(mutex_);
            STATS_EVENT_UPDATE_LRU();
            list.update_lru(node, t);
        }
    }

    void try_update_unstamped(ListNode *const node)
    {
        int64_t const t = ListNode::wall_clock();
        if (!node->check_lru_time(t, ListNode::LRU_UPDATE_PERIOD)) {
            return;
        }
        std::unique_lock const l(mutex_);
        // re-check under the lock: a finalize may have stamped it
        if (node->stamped_ || !node->is_in_list()) {
            return;
        }
        STATS_EVENT_UPDATE_LRU();
        if (node->negative_) {
            negative_lru_.update_lru(node, t);
        }
        else {
            lru_.delink(node);
            lru_.insert_after(&boundary_, node);
            node->update_lru_time(t);
        }
    }

    // Value transition at finalize (created or deleted). A stamped entry
    // keeps its place and stamp and only changes its value flag; an unstamped
    // one flips between the negative list and the unstamped region.
    void transition(ListNode *const node, bool const negative)
    {
        {
            std::unique_lock const l(mutex_);
            if (!node->is_in_list()) {
                return; // being evicted concurrently
            }
            if (node->stamped_) {
                node->negative_ = negative;
                stamped_negative_.fetch_add(
                    negative ? 1 : static_cast<size_t>(-1),
                    std::memory_order_relaxed);
                return;
            }
            (node->negative_ ? negative_lru_ : lru_).delink(node);
            node->negative_ = negative;
            // negative recency restarts; a fresh live entry is unstamped
            node->update_lru_time(negative ? ListNode::wall_clock() : 0);
            if (negative) {
                negative_lru_.push_front(node);
            }
            else {
                lru_.insert_after(&boundary_, node);
            }
        }
        if (negative) {
            size_.fetch_sub(1, std::memory_order_acq_rel);
            size_t const sz =
                1 + negative_size_.fetch_add(1, std::memory_order_acq_rel);
            if (sz > negative_max_ && evict_negative()) {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }
        else {
            negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            size_t const sz = 1 + size_.fetch_add(1, std::memory_order_acq_rel);
            if (sz > max_size_ && evict()) {
                size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }
    }

    void finish_insert(ListNode *node)
    {
        if (node->negative_) {
            {
                std::unique_lock const l(mutex_);
                STATS_EVENT_INSERT_NEW();
                negative_lru_.push_front(node);
                node->update_lru_time(ListNode::wall_clock());
            }
            size_t const sz =
                1 + negative_size_.fetch_add(1, std::memory_order_acq_rel);
            if (sz > negative_max_ && evict_negative()) {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
            return;
        }
        size_t sz = size();
        bool const evicted = (sz >= max_size_) && evict();
        {
            std::unique_lock const l(mutex_);
            STATS_EVENT_INSERT_NEW();
            if (stamp_mode_) {
                lru_.insert_after(&boundary_, node); // unstamped region
            }
            else {
                lru_.push_front(node);
            }
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

    // Evict the tail of `list`. The map accessor is taken before the node
    // leaves the list, and the node is delinked only if it is still the tail
    // once the accessor is held: a reader that found the entry in the map
    // therefore either sees it in the list (and can promote it, after which
    // the eviction moves on to the new tail) or does not find it at all. An
    // entry a block read can thus never vanish before finalize stamps it.
    // Returns false when the list is empty.
    bool evict_from(LruList &list, ListNode *const skip)
    {
        while (true) {
            Key key;
            ListNode *target;
            {
                std::unique_lock const l(mutex_);
                target = list.tail_skipping(skip);
                if (target == nullptr) {
                    return false;
                }
                key = target->key_;
            }
            Accessor acc;
            if (!hmap_.find(acc, key) || acc->second.node_ != target) {
                continue; // evicted by another thread meanwhile
            }
            bool stamped_negative = false;
            {
                std::unique_lock const l(mutex_);
                if (!target->is_in_list() ||
                    list.tail_skipping(skip) != target) {
                    continue; // promoted (or gone) meanwhile: retry
                }
                STATS_EVENT_EVICT();
                if (stamp_mode_ && target->stamped_) {
                    // unstamped entries drain first, then stamps oldest first,
                    // so a cached victim means the cached set outgrew the
                    // physical capacity — a consensus bug, not a perf bug
                    uint64_t const stamp = static_cast<uint64_t>(
                        target->lru_time_.load(std::memory_order_acquire));
                    MONAD_ASSERT(
                        stamp < evict_floor_.load(std::memory_order_relaxed));
                    stamped_negative = target->negative_;
                }
                list.delink(target);
            }
            if (stamped_negative) {
                stamped_negative_.fetch_sub(1, std::memory_order_relaxed);
            }
            hmap_.erase(acc);
            pool_.delete_obj(target);
            return true;
        }
    }

    bool evict()
    {
        return evict_from(lru_, stamp_mode_ ? &boundary_ : nullptr);
    }

    bool evict_negative()
    {
        return evict_from(negative_lru_, nullptr);
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
        bool negative_{false}; // the key holds no value
        bool stamped_{false}; // in the stamped region; time is the stamp

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
            insert_after(&head_, node);
        }

        void insert_after(ListNode *const pos, ListNode *const node)
        {
            ListNode *const next = pos->next_;
            node->prev_ = pos;
            node->next_ = next;
            next->prev_ = node;
            pos->next_ = node;
        }

        // The tail, or the node before `skip` when the tail is the sentinel
        // `skip` itself; nullptr when empty. Does not delink.
        ListNode *tail_skipping(ListNode *const skip)
        {
            ListNode *target = tail_.prev_;
            if (skip != nullptr && target == skip) {
                target = skip->prev_;
            }
            return target == &head_ ? nullptr : target;
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
