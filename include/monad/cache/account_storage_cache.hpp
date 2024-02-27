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
    class LruList;
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
    using AccountAccessor = typename AccountMap::accessor;
    using StorageAccessor = typename StorageMap::accessor;
    using AccountConstAccessor = typename AccountMap::const_accessor;
    using StorageConstAccessor = typename StorageMap::const_accessor;

private:
    /// ListNode
    template <class Finder>
    struct ListNode
    {
        static constexpr uint64_t one_second = 1'000'000'000;
        static constexpr uint64_t lru_update_period = 1 * one_second;

        ListNode *prev_{nullptr};
        ListNode *next_{nullptr};
        Finder finder_;
        uint64_t lru_time_;

        ListNode() {}

        ListNode(Finder &finder)
            : finder_(finder)
        {
        }

        bool is_in_list() const
        {
            return prev_ != nullptr;
        }

        void update_time()
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

        void update_lru(Node *node)
        {
            if (node->is_in_list()) {
                delink_node(node);
                push_front_node(node);
                node->update_time();
            } // else item is being evicted, don't update LRU
        }

        void delink_node(Node *node)
        {
            Node *prev = node->prev_;
            Node *next = node->next_;
            prev->next_ = next;
            next->prev_ = prev;
            node->prev_ = nullptr;
        }

        void push_front_node(Node *node)
        {
            Node *head = head_.next_;
            node->prev_ = &head_;
            node->next_ = head;
            head->prev_ = node;
            head_.next_ = node;
        }

        Node *evict_lru_node()
        {
            Node *target = tail_.prev_;
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

    /// StorageMapWrapper
    struct StorageMapWrapper
    {
        AccountStorageCache &cache_;
        HashMap<bytes32_t, StorageMapValue> map_;

        StorageMapWrapper(AccountStorageCache &cache)
            : cache_(cache)
        {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            cache_.stats_.event_storage_map_ctor();
#endif
        }

        ~StorageMapWrapper()
        {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            cache_.stats_.event_storage_map_dtor();
#endif
        }
    };

    /// AccountFinder
    struct AccountFinder
    {
        Address addr_;
    };

    /// StorageFinder
    struct StorageFinder
    {
        std::shared_ptr<StorageMapWrapper> storage_;
        bytes32_t key_;

        StorageFinder() {}

        StorageFinder(
            std::shared_ptr<StorageMapWrapper> const &storage, bytes32_t key)
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
    AccountStorageCache(size_t account_max_size, size_t storage_max_size)
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
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_account_find_miss();
#endif
            return false;
        }
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
        stats_.event_account_find_hit();
#endif
        auto node = acc->second.node_;
        try_update_lru(node, account_lru_, account_mutex_);
        return true;
    }

    bool insert_account(
        AccountAccessor &acc, Address const &addr,
        std::optional<Account> const &account)
    {
        AccountMapKeyValue kv(addr, AccountMapValue(nullptr, nullptr, account));
        if (!account_map_.insert(acc, kv)) {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_account_insert_found();
#endif
            acc->second.value_ = account;
            if (account == std::nullopt) {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
                if (acc->second.storage_) {
                    stats_.event_account_storage_reset();
                }
#endif
                acc->second.storage_.reset();
            }
            AccountNode *node = acc->second.node_;
            try_update_lru(node, account_lru_, account_mutex_);
            return false;
        }
        AccountNode *node = account_pool_.new_obj(AccountFinder(addr));
        acc->second.node_ = node;
        finish_account_insert(node);
        return true;
    }

    bool find_storage(
        StorageConstAccessor &acc, Address const &addr, bytes32_t const &key)
    {
        AccountConstAccessor account_acc{};
        if (account_map_.find(account_acc, addr)) {
            auto &storage = account_acc->second.storage_;
            if ((storage) && (storage->map_.find(acc, key))) {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
                stats_.event_storage_find_hit();
#endif
                StorageNode *node = acc->second.node_;
                try_update_lru(node, storage_lru_, storage_mutex_);
                return true;
            }
        }
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
        stats_.event_storage_find_miss();
#endif
        return false;
    }

    bool insert_storage(
        AccountAccessor &account_acc, bytes32_t const &key,
        bytes32_t const &value)
    {
        MONAD_ASSERT(!account_acc.empty());
        auto &storage = account_acc->second.storage_;
        if (!storage) {
            storage = std::make_shared<StorageMapWrapper>(*this);
        }
        StorageAccessor storage_acc{};
        StorageMapKeyValue kv(key, StorageMapValue(nullptr, value));
        if (!storage->map_.insert(storage_acc, kv)) {
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_storage_insert_found();
#endif
            storage_acc->second.value_ = value;
            StorageNode *node = storage_acc->second.node_;
            try_update_lru(node, storage_lru_, storage_mutex_);
            return false;
        }
        // Note: Copies shared_ptr to storage map.
        StorageNode *node = storage_pool_.new_obj(StorageFinder(storage, key));
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
    void try_update_lru(Node *node, List &list, Mutex &mutex)
    {
        if (node->check_lru_time()) {
            std::unique_lock l(mutex);
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            if (std::is_same<Node, AccountNode>::value) {
                stats_.event_account_update_lru();
            }
            else {
                stats_.event_storage_update_lru();
            }
#endif
            list.update_lru(node);
        }
    }

    void finish_account_insert(AccountNode *node)
    {
        size_t sz = account_size();
        bool evicted = false;
        if (sz >= account_max_size_) {
            account_evict();
            evicted = true;
        }
        {
            std::unique_lock l(account_mutex_);
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_account_insert_new();
#endif
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

    void finish_storage_insert(StorageNode *node)
    {
        size_t sz = storage_size();
        bool evicted = false;
        if (sz >= storage_max_size_) {
            storage_evict();
            evicted = true;
        }
        {
            std::unique_lock l(storage_mutex_);
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_storage_insert_new();
#endif
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
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_account_evict();
#endif
            target = account_lru_.evict_lru_node();
        }
        {
            AccountFinder &finder = target->finder_;
            AccountAccessor acc;
            bool found = account_map_.find(acc, finder.addr_);
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
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
            stats_.event_storage_evict();
#endif
            target = storage_lru_.evict_lru_node();
        }
        {
            MONAD_ASSERT(target);
            StorageFinder &finder = target->finder_;
            MONAD_ASSERT(finder.storage_);
            StorageMap &map = finder.storage_->map_;
            StorageAccessor acc;
            bool found = map.find(acc, finder.key_);
            MONAD_ASSERT(found);
            map.erase(acc);
        }
        storage_pool_.delete_obj(target);
    }

public:
    std::string print_stats()
    {
        std::string str;
#ifdef MONAD_ACCOUNT_STORAGE_CACHE_STATS
        str = stats_.print_account_stats();
        if constexpr (std::is_same<Mutex, SpinLock>::value) {
            str += " _ " + account_mutex_.print_stats();
        }
        str += " - " + account_pool_.print_stats();
        str += " ** " + stats_.print_storage_stats();
        if constexpr (std::is_same<Mutex, SpinLock>::value) {
            str += " _ " + storage_mutex_.print_stats();
        }
        str += " - " + storage_pool_.print_stats();
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

        void event_account_update_lru()
        {
            ++n_account_update_lru_;
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

        void event_storage_update_lru()
        {
            ++n_storage_update_lru_;
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
