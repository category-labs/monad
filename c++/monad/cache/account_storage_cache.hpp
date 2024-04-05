#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/mem/batch_mem_pool.hpp>
#include <monad/synchronization/spin_lock.hpp>

#include <quill/Quill.h>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <mutex>

MONAD_NAMESPACE_BEGIN

class AccountStorageCache
{
    /// TYPES
    template <class Finder>
    struct ListNode;
    template <class Node>
    struct LruList;
    struct StorageMapWrapper;
    struct AccountFinder;
    struct StorageFinder;
    struct AccountMapValue;
    struct StorageMapValue;

    template <class Key, class Value>
    using HashMap = tbb::concurrent_hash_map<Key, Value>;
    using Mutex = SpinLock;
    using AccountNode = ListNode<AccountFinder>;
    using StorageNode = ListNode<StorageFinder>;
    using AccountMap = HashMap<Address, AccountMapValue>;
    using StorageMap = HashMap<bytes32_t, StorageMapValue>;
    using AccountMapKeyValue = std::pair<Address, AccountMapValue>;
    using StorageMapKeyValue = std::pair<bytes32_t, StorageMapValue>;
    using AccountList = LruList<AccountNode>;
    using StorageList = LruList<StorageNode>;
    using AccountPool = BatchMemPool<AccountNode>;
    using StoragePool = BatchMemPool<StorageNode>;

public:
    using AccountAccessor = AccountMap::accessor;
    using StorageAccessor = StorageMap::accessor;
    using AccountConstAccessor = AccountMap::const_accessor;
    using StorageConstAccessor = StorageMap::const_accessor;

private:
    /// ListNode
    template <class Finder>
    struct ListNode
    {
        static constexpr int64_t one_second = 1'000'000'000L;
        static constexpr int64_t lru_update_period = 1 * one_second;

        ListNode *prev_{nullptr};
        ListNode *next_{nullptr};
        Finder const finder_;
        std::atomic<int64_t> lru_time_;

        ListNode() {}

        ListNode(Finder const &finder)
            : finder_(finder)
        {
        }

        bool is_in_list() const
        {
            return prev_ != nullptr;
        }

        void update_time()
        {
            lru_time_.store(cur_time(), std::memory_order_release);
        }

        bool check_lru_time() const
        {
            int64_t lru_time = lru_time_.load(std::memory_order_acquire);
            return (cur_time() - lru_time) >= lru_update_period;
        }

        int64_t cur_time() const
        {
            return std::chrono::duration_cast<std::chrono::nanoseconds>(
                       std::chrono::system_clock::now().time_since_epoch())
                .count();
        }
    }; /// ListNode

    /// LruList
    template <class Node>
    struct LruList
    {
        using Pool = BatchMemPool<Node>;

        Node head_;
        Node tail_;

        LruList()
        {
            head_.next_ = &tail_;
            tail_.prev_ = &head_;
        }

        void update_lru(Node *const node)
        {
            if (node->is_in_list()) {
                delink_node(node);
                push_front_node(node);
                node->update_time();
            } // else item is being evicted, don't update LRU
        }

        void delink_node(Node *const node)
        {
            Node *const prev = node->prev_;
            Node *const next = node->next_;
            prev->next_ = next;
            next->prev_ = prev;
            node->prev_ = nullptr;
        }

        void push_front_node(Node *const node)
        {
            Node *const head = head_.next_;
            node->prev_ = &head_;
            node->next_ = head;
            head->prev_ = node;
            head_.next_ = node;
        }

        Node *evict_lru_node()
        {
            Node *const target = tail_.prev_;
            MONAD_ASSERT(target != &head_);
            delink_node(target);
            return target;
        }

        void clear_list(Pool &pool)
        {
            Node *node = head_.next_;
            Node *next;
            while (node != &tail_) {
                next = node->next_;
                pool.delete_obj(node);
                node = next;
            }
            head_.next_ = &tail_;
            tail_.prev_ = &head_;
        }
    }; /// LruList

/// STATS MACROS
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
    #define STATS_EVENT_ACCOUNT_EVICT() stats_.event_account_evict();
    #define STATS_EVENT_ACCOUNT_FIND_HIT() stats_.event_account_find_hit();
    #define STATS_EVENT_ACCOUNT_FIND_MISS() stats_.event_account_find_miss();
    #define STATS_EVENT_ACCOUNT_INSERT_FOUND()                                 \
        stats_.event_account_insert_found();
    #define STATS_EVENT_ACCOUNT_INSERT_NEW() stats_.event_account_insert_new();
    #define STATS_EVENT_ACCOUNT_STORAGE_RESET()                                \
        stats_.event_account_storage_reset();
    #define STATS_EVENT_STORAGE_EVICT() stats_.event_storage_evict();
    #define STATS_EVENT_STORAGE_FIND_HIT() stats_.event_storage_find_hit()
    #define STATS_EVENT_STORAGE_FIND_MISS() stats_.event_storage_find_miss()
    #define STATS_EVENT_STORAGE_INSERT_FOUND()                                 \
        stats_.event_storage_insert_found()
    #define STATS_EVENT_STORAGE_INSERT_NEW() stats_.event_storage_insert_new()
    #define STATS_EVENT_STORAGE_MAP_CTOR()                                     \
        cache_.stats_.event_storage_map_ctor()
    #define STATS_EVENT_STORAGE_MAP_DTOR()                                     \
        cache_.stats_.event_storage_map_dtor()
    #define STATS_EVENT_UPDATE_LRU() stats_.event_update_lru<Node>()
#else
    #define STATS_EVENT_ACCOUNT_EVICT()
    #define STATS_EVENT_ACCOUNT_FIND_HIT()
    #define STATS_EVENT_ACCOUNT_FIND_MISS()
    #define STATS_EVENT_ACCOUNT_INSERT_FOUND()
    #define STATS_EVENT_ACCOUNT_INSERT_NEW()
    #define STATS_EVENT_ACCOUNT_STORAGE_RESET()
    #define STATS_EVENT_STORAGE_EVICT()
    #define STATS_EVENT_STORAGE_MAP_CTOR()
    #define STATS_EVENT_STORAGE_FIND_HIT()
    #define STATS_EVENT_STORAGE_FIND_MISS()
    #define STATS_EVENT_STORAGE_INSERT_FOUND()
    #define STATS_EVENT_STORAGE_INSERT_NEW()
    #define STATS_EVENT_STORAGE_MAP_DTOR()
    #define STATS_EVENT_UPDATE_LRU()
#endif

    /// StorageMapWrapper
    struct StorageMapWrapper
    {
        AccountStorageCache &cache_;
        HashMap<bytes32_t, StorageMapValue> map_;

        StorageMapWrapper(AccountStorageCache &cache)
            : cache_(cache)
        {
            STATS_EVENT_STORAGE_MAP_CTOR();
        }

        ~StorageMapWrapper()
        {
            STATS_EVENT_STORAGE_MAP_DTOR();
        }
    };

    /// AccountFinder
    struct AccountFinder
    {
        Address const addr_;
    };

    /// StorageFinder
    struct StorageFinder
    {
        std::shared_ptr<StorageMapWrapper> const storage_;
        bytes32_t const key_;

        StorageFinder() {}

        StorageFinder(
            std::shared_ptr<StorageMapWrapper> const &storage,
            bytes32_t const &key)
            : storage_(storage)
            , key_(key)
        {
        }
    };

    /// AccountMapValue
    struct AccountMapValue
    {
        AccountNode *node_;
        std::shared_ptr<StorageMapWrapper> storage_;
        std::optional<Account> value_;
    };

    /// StorageMapValue
    struct StorageMapValue
    {
        StorageNode *node_;
        bytes32_t value_;
    };

    /// Constants
    static constexpr size_t slack = 16;
    static constexpr size_t line_align = 64;

    /// DATA
    alignas(line_align) size_t const account_max_size_;
    size_t const storage_max_size_;
    AccountMap account_map_;
    alignas(line_align) Mutex account_mutex_;
    AccountList account_lru_;
    alignas(line_align) Mutex storage_mutex_;
    StorageList storage_lru_;
    alignas(line_align) std::atomic<size_t> account_size_{0};
    AccountPool account_pool_;
    alignas(line_align) std::atomic<size_t> storage_size_{0};
    StoragePool storage_pool_;

public:
    AccountStorageCache(
        size_t const account_max_size, size_t const storage_max_size)
        : account_max_size_(account_max_size)
        , storage_max_size_(storage_max_size)
        , account_map_(account_max_size_ + slack)
        , account_pool_(account_max_size + slack)
        , storage_pool_(storage_max_size + slack)
    {
    }

    AccountStorageCache(AccountStorageCache const &) = delete;
    AccountStorageCache &operator=(AccountStorageCache const &) = delete;

    ~AccountStorageCache()
    {
        clear();
    }

    template <class Accessor>
    bool find_account(Accessor &acc, Address const &addr)
    {
        if (!account_map_.find(acc, addr)) {
            STATS_EVENT_ACCOUNT_FIND_MISS();
            return false;
        }
        STATS_EVENT_ACCOUNT_FIND_HIT();
        AccountNode *const node = acc->second.node_;
        try_update_lru(node, account_lru_, account_mutex_);
        return true;
    }

    bool insert_account(
        AccountAccessor &acc, Address const &addr,
        std::optional<Account> const &account)
    {
        AccountMapKeyValue const kv(
            addr, AccountMapValue(nullptr, nullptr, account));
        if (!account_map_.insert(acc, kv)) {
            STATS_EVENT_ACCOUNT_INSERT_FOUND();
            acc->second.value_ = account;
            if (account == std::nullopt) {
                if (acc->second.storage_) {
                    STATS_EVENT_ACCOUNT_STORAGE_RESET();
                }
                acc->second.storage_.reset();
            }
            AccountNode *const node = acc->second.node_;
            try_update_lru(node, account_lru_, account_mutex_);
            return false;
        }
        AccountNode *const node = account_pool_.new_obj(AccountFinder(addr));
        acc->second.node_ = node;
        finish_account_insert(node);
        return true;
    }

    bool find_storage(
        StorageConstAccessor &acc, Address const &addr, bytes32_t const &key)
    {
        AccountConstAccessor account_acc{};
        if (account_map_.find(account_acc, addr)) {
            std::shared_ptr<StorageMapWrapper> const &storage =
                account_acc->second.storage_;
            if ((storage) && (storage->map_.find(acc, key))) {
                STATS_EVENT_STORAGE_FIND_HIT();
                StorageNode *const node = acc->second.node_;
                try_update_lru(node, storage_lru_, storage_mutex_);
                return true;
            }
        }
        STATS_EVENT_STORAGE_FIND_MISS();
        return false;
    }

    bool insert_storage(
        AccountAccessor &account_acc, bytes32_t const &key,
        bytes32_t const &value)
    {
        MONAD_ASSERT(!account_acc.empty());
        std::shared_ptr<StorageMapWrapper> &storage =
            account_acc->second.storage_;
        if (!storage) {
            storage = std::make_shared<StorageMapWrapper>(*this);
        }
        StorageAccessor storage_acc{};
        StorageMapKeyValue const kv(key, StorageMapValue(nullptr, value));
        if (!storage->map_.insert(storage_acc, kv)) {
            STATS_EVENT_STORAGE_INSERT_FOUND();
            storage_acc->second.value_ = value;
            StorageNode *const node = storage_acc->second.node_;
            try_update_lru(node, storage_lru_, storage_mutex_);
            return false;
        }
        // Note: Copies shared_ptr to storage map.
        StorageNode *const node =
            storage_pool_.new_obj(StorageFinder(storage, key));
        storage_acc->second.node_ = node;
        storage_acc.release();
        finish_storage_insert(node);
        return true;
    }

    void clear() // Not thread-safe with other cache operations
    {
        storage_lru_.clear_list(storage_pool_);
        account_lru_.clear_list(account_pool_);
        account_map_.clear();
        account_size_.store(0, std::memory_order_release);
        storage_size_.store(0, std::memory_order_release);
    }

    size_t account_size() const
    {
        return account_size_.load(std::memory_order_acquire);
    }

    size_t storage_size() const
    {
        return storage_size_.load(std::memory_order_acquire);
    }

private:
    template <class Node, class List>
    void try_update_lru(Node *const node, List &list, Mutex &mutex)
    {
        if (node->check_lru_time()) {
            std::unique_lock l(mutex);
            STATS_EVENT_UPDATE_LRU();
            list.update_lru(node);
        }
    }

    void finish_account_insert(AccountNode *const node)
    {
        size_t sz = account_size();
        bool evicted = false;
        if (sz >= account_max_size_) {
            account_evict();
            evicted = true;
        }
        {
            std::unique_lock l(account_mutex_);
            STATS_EVENT_ACCOUNT_INSERT_NEW();
            account_lru_.push_front_node(node);
        }
        if (!evicted) {
            sz = 1 + account_size_.fetch_add(1, std::memory_order_acq_rel);
        }
        if (sz > account_max_size_) {
            if (account_size_.compare_exchange_strong(
                    sz,
                    sz - 1,
                    std::memory_order_acq_rel,
                    std::memory_order_relaxed)) {
                account_evict();
            }
        }
    }

    void finish_storage_insert(StorageNode *const node)
    {
        size_t sz = storage_size();
        bool evicted = false;
        if (sz >= storage_max_size_) {
            storage_evict();
            evicted = true;
        }
        {
            std::unique_lock l(storage_mutex_);
            STATS_EVENT_STORAGE_INSERT_NEW();
            storage_lru_.push_front_node(node);
        }
        if (!evicted) {
            sz = 1 + storage_size_.fetch_add(1, std::memory_order_acq_rel);
        }
        if (sz > storage_max_size_) {
            if (storage_size_.compare_exchange_strong(
                    sz,
                    sz - 1,
                    std::memory_order_acq_rel,
                    std::memory_order_relaxed)) {
                storage_evict();
            }
        }
    }

    void account_evict()
    {
        AccountNode *target;
        {
            std::unique_lock l(account_mutex_);
            STATS_EVENT_ACCOUNT_EVICT();
            target = account_lru_.evict_lru_node();
        }
        {
            AccountFinder const &finder = target->finder_;
            AccountAccessor acc;
            bool const found = account_map_.find(acc, finder.addr_);
            MONAD_ASSERT(found);
            account_map_.erase(acc);
        }
        account_pool_.delete_obj(target);
    }

    void storage_evict()
    {
        StorageNode *target;
        {
            std::unique_lock l(storage_mutex_);
            STATS_EVENT_STORAGE_EVICT();
            target = storage_lru_.evict_lru_node();
        }
        {
            MONAD_ASSERT(target);
            StorageFinder const &finder = target->finder_;
            MONAD_ASSERT(finder.storage_);
            StorageMap &map = finder.storage_->map_;
            StorageAccessor acc;
            bool const found = map.find(acc, finder.key_);
            MONAD_ASSERT(found);
            map.erase(acc);
        }
        storage_pool_.delete_obj(target);
    }

/// STATS
#undef STATS_EVENT_ACCOUNT_EVICT
#undef STATS_EVENT_ACCOUNT_FIND_HIT
#undef STATS_EVENT_ACCOUNT_FIND_MISS
#undef STATS_EVENT_ACCOUNT_INSERT_FOUND
#undef STATS_EVENT_ACCOUNT_INSERT_NEW
#undef STATS_EVENT_ACCOUNT_STORAGE_RESET
#undef STATS_EVENT_STORAGE_EVICT
#undef STATS_EVENT_STORAGE_FIND_HIT
#undef STATS_EVENT_STORAGE_FIND_MISS
#undef STATS_EVENT_STORAGE_INSERT_FOUND
#undef STATS_EVENT_STORAGE_INSERT_NEW
#undef STATS_EVENT_STORAGE_MAP_CTOR
#undef STATS_EVENT_STORAGE_MAP_DTOR
#undef STATS_EVENT_UPDATE_LRU

public:
    std::string print_stats()
    {
        std::string str;
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
        str = stats_.print_account_stats();
        if constexpr (std::is_same<Mutex, SpinLock>::value) {
            str += " , " + account_mutex_.print_stats();
        }
        str += " , " + account_pool_.print_stats();
        str += " ** " + stats_.print_storage_stats();
        if constexpr (std::is_same<Mutex, SpinLock>::value) {
            str += " , " + storage_mutex_.print_stats();
        }
        str += " , " + storage_pool_.print_stats();
        stats_.clear_stats();
#endif
        return str;
    }

private:
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
    /// CacheStats
    struct CacheStats
    {
        std::atomic<uint64_t> n_account_find_hit_{0};
        std::atomic<uint64_t> n_account_find_miss_{0};
        std::atomic<uint64_t> n_account_insert_found_{0};
        uint64_t n_account_insert_new_{0};
        uint64_t n_account_evict_{0};
        uint64_t n_account_update_lru_{0};
        std::atomic<uint64_t> n_storage_find_hit_{0};
        std::atomic<uint64_t> n_storage_find_miss_{0};
        std::atomic<uint64_t> n_storage_insert_found_{0};
        uint64_t n_storage_insert_new_{0};
        uint64_t n_storage_evict_{0};
        uint64_t n_storage_update_lru_{0};
        std::atomic<uint64_t> n_account_storage_reset_{0};
        std::atomic<uint64_t> n_storage_map_ctor_{0};
        std::atomic<uint64_t> n_storage_map_dtor_{0};

        void event_account_find_hit()
        {
            n_account_find_hit_.fetch_add(1, std::memory_order_release);
        }

        void event_account_find_miss()
        {
            n_account_find_miss_.fetch_add(1, std::memory_order_release);
        }

        void event_account_insert_found()
        {
            n_account_insert_found_.fetch_add(1, std::memory_order_release);
        }

        void event_account_insert_new()
        {
            ++n_account_insert_new_;
        }

        void event_account_evict()
        {
            ++n_account_evict_;
        }

        void event_storage_find_hit()
        {
            n_storage_find_hit_.fetch_add(1, std::memory_order_release);
        }

        void event_storage_find_miss()
        {
            n_storage_find_miss_.fetch_add(1, std::memory_order_release);
        }

        void event_storage_insert_found()
        {
            n_storage_insert_found_.fetch_add(1, std::memory_order_release);
        }

        void event_storage_insert_new()
        {
            ++n_storage_insert_new_;
        }

        void event_storage_evict()
        {
            ++n_storage_evict_;
        }

        template <class Node>
        void event_update_lru()
        {
            if (std::same_as<Node, AccountNode>) {
                ++n_account_update_lru_;
            }
            else {
                ++n_storage_update_lru_;
            }
        }

        void event_account_storage_reset()
        {
            n_account_storage_reset_.fetch_add(1, std::memory_order_release);
        }

        void event_storage_map_ctor()
        {
            n_storage_map_ctor_.fetch_add(1, std::memory_order_release);
        }

        void event_storage_map_dtor()
        {
            n_storage_map_dtor_.fetch_add(1, std::memory_order_release);
        }

        void clear_stats()
        {
            // Not called concurrently with cache operations.
            n_account_find_hit_.store(0, std::memory_order_release);
            n_account_find_miss_.store(0, std::memory_order_release);
            n_account_insert_found_.store(0, std::memory_order_release);
            n_account_insert_new_ = 0;
            n_account_evict_ = 0;
            n_account_update_lru_ = 0;
            n_storage_find_hit_.store(0, std::memory_order_release);
            n_storage_find_miss_.store(0, std::memory_order_release);
            n_storage_insert_found_.store(0, std::memory_order_release);
            n_storage_insert_new_ = 0;
            n_storage_evict_ = 0;
            n_storage_update_lru_ = 0;
            n_account_storage_reset_.store(0, std::memory_order_release);
            n_storage_map_ctor_.store(0, std::memory_order_release);
            n_storage_map_dtor_.store(0, std::memory_order_release);
        }

        std::string print_account_stats()
        {
            char str[100];
            sprintf(
                str,
                "%6ld %5ld %6ld %5ld %5ld %5ld"
                "%s",
                n_account_find_hit_.load(std::memory_order_acquire),
                n_account_find_miss_.load(std::memory_order_acquire),
                n_account_insert_found_.load(std::memory_order_acquire),
                n_account_insert_new_,
                n_account_evict_,
                n_account_update_lru_,
                "");
            return std::string(str);
        }

        std::string print_storage_stats()
        {
            char str[100];
            sprintf(
                str,
                "%6ld %5ld %6ld %5ld %5ld %5ld . %4ld %4ld %4ld"
                "%s",
                n_storage_find_hit_.load(std::memory_order_acquire),
                n_storage_find_miss_.load(std::memory_order_acquire),
                n_storage_insert_found_.load(std::memory_order_acquire),
                n_storage_insert_new_,
                n_storage_evict_,
                n_storage_update_lru_,
                n_account_storage_reset_.load(std::memory_order_acquire),
                n_storage_map_ctor_.load(std::memory_order_acquire),
                n_storage_map_dtor_.load(std::memory_order_acquire),
                "");
            return std::string(str);
        }
    }; /// CacheStats

    CacheStats stats_;
#endif // MONAD_ACCOUNT_STORAGE_CACHE_STATS

}; /// AccountStorageCache

MONAD_NAMESPACE_END
