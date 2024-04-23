#pragma once

#include <monad/core/assert.h>
#include <monad/mem/batch_mem_pool.hpp>
#include <monad/synchronization/spin_lock.hpp>

#include <quill/Quill.h>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <string>

MONAD_NAMESPACE_BEGIN

template <class Key, class Value>
class LruCache
{
    /// TYPES
    struct ListNode;
    struct HashMapValue;
    struct LruList;
    using HashMap = tbb::concurrent_hash_map<Key, HashMapValue>;
    using HashMapKeyValue = std::pair<Key, HashMapValue>;
    using Accessor = HashMap::accessor;
    using Mutex = SpinLock;
    using Pool = BatchMemPool<ListNode>;

    /// CONSTANTS
    static constexpr size_t slack = 16;

    /// DATA
    size_t max_size_;
    std::atomic<size_t> size_;
    LruList lru_;
    Mutex mutex_;
    HashMap hmap_;
    Pool pool_;

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

    explicit LruCache(size_t const max_size)
        : max_size_(max_size)
        , size_(0)
        , hmap_(max_size + slack)
        , pool_(max_size + slack, 1)
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
        ListNode *const node = acc->second.node_;
        try_update_lru(node);
        return true;
    }

    bool insert(Key const &key, Value const &value)
    {
        Accessor acc;
        HashMapKeyValue const hmkv(key, HashMapValue(value, nullptr));
        if (!hmap_.insert(acc, hmkv)) {
            STATS_EVENT_INSERT_FOUND();
            acc->second.value_ = value;
            ListNode *const node = acc->second.node_;
            try_update_lru(node);
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
        if (node->check_lru_time()) {
            std::unique_lock l(mutex_);
            STATS_EVENT_UPDATE_LRU();
            lru_.update_lru(node);
        }
    }

    void finish_insert(ListNode *node)
    {
        size_t sz = size();
        bool evicted = false;
        if (sz >= max_size_) {
            evict();
            evicted = true;
        }
        {
            std::unique_lock l(mutex_);
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
                evict();
            }
        }
    }

    void evict()
    {
        ListNode *target;
        {
            std::unique_lock l(mutex_);
            STATS_EVENT_EVICT();
            target = lru_.evict();
        }
        Accessor acc;
        bool const found = hmap_.find(acc, target->key_);
        MONAD_ASSERT(found);
        hmap_.erase(acc);
        pool_.delete_obj(target);
    }

    /// ListNode
    struct ListNode
    {
        static constexpr uint64_t one_second = 1'000'000'000;
        static constexpr uint64_t lru_update_period = 1 * one_second;

        ListNode *prev_{nullptr};
        ListNode *next_{nullptr};
        Key key_;
        uint64_t lru_time_;

        ListNode() {}

        ListNode(Key const &key)
            : key_(key)
        {
        }

        bool isInList() const
        {
            return prev_ != nullptr;
        }

        void update_lru_time()
        {
            lru_time_ = cur_time();
        }

        bool check_lru_time() const
        {
            return (cur_time() - lru_time_) >= lru_update_period;
        }

        uint64_t cur_time() const
        {
            return std::chrono::duration_cast<std::chrono::nanoseconds>(
                       std::chrono::system_clock::now().time_since_epoch())
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

        void update_lru(ListNode *node)
        {
            if (node->isInList()) {
                delink(node);
                push_front(node);
                node->update_lru_time();
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
            MONAD_ASSERT(target != &head_);
            delink(target);
            return target;
        }
    }; /// LruList

    /// HashMapValue
    struct HashMapValue
    {
        Value value_;
        ListNode *node_;

        HashMapValue() {}

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
        std::string str;
#ifdef MONAD_LRU_CACHE_STATS
        str = stats_.print_stats();
        if constexpr (std::same_as<Mutex, SpinLock>) {
            str += " " + mutex_.print_stats();
        }
        str += " " + pool_.print_stats();
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
            char str[100];
            sprintf(
                str,
                "%6ld %5ld %6ld %5ld %5ld %5ld",
                n_find_hit_.load(std::memory_order_acquire),
                n_find_miss_.load(std::memory_order_acquire),
                n_insert_found_.load(std::memory_order_acquire),
                n_insert_new_,
                n_evict_,
                n_update_lru_);
            clear_stats();
            return std::string(str);
        }
    }; /// CacheStats

    CacheStats stats_;
#endif /// MONAD_LRU_CACHE_STATS

}; /// LruCache

MONAD_NAMESPACE_END
