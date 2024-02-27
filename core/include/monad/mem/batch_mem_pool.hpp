#pragma once

#include <monad/synchronization/spin_lock.hpp>

#include <mutex>
#include <new>
#include <string>

MONAD_NAMESPACE_BEGIN

/// Memory pool for objects of type 'T' that supports preallocation
/// and batch allocation. It grows but does not shrink. Memory is
/// deallocated at the destruction of the pool.

template <class T>
class BatchMemPool
{
    /// TYPES
    using Mutex = SpinLock;

    using Space = std::aligned_storage_t<
        std::max(sizeof(T), sizeof(void *)),
        std::max(alignof(T), alignof(void *))>;

    struct FreeNode
    {
        FreeNode *next_;
    };

    static_assert(std::is_trivially_destructible<FreeNode>::value);

    static_assert(sizeof(Space) >= sizeof(T));
    static_assert(sizeof(Space) >= sizeof(FreeNode));
    static_assert(alignof(Space) >= alignof(T));
    static_assert(alignof(Space) >= alignof(FreeNode));

    /// CONSTANTS
    static constexpr size_t default_batch_size = 1000;

    /// DATA
    Mutex mutex_;
    FreeNode *free_{nullptr};
    size_t batch_;

/// STATS MACROS
#ifdef MONAD_BATCH_MEM_POOL_STATS
    #define STATS_EVENT_ALLOC(x) stats_.event_alloc(x)
    #define STATS_EVENT_DELETE() stats_.event_delete()
    #define STATS_EVENT_NEW() stats_.event_new()
#else
    #define STATS_EVENT_ALLOC(x)
    #define STATS_EVENT_DELETE()
    #define STATS_EVENT_NEW()
#endif

public:
    BatchMemPool(
        size_t const initial = 0, size_t const batch = default_batch_size)
        : batch_(batch)
    {
        alloc_batch(initial);
    }

    ~BatchMemPool()
    {
        free_all();
    }

    template <class... Args>
    T *new_obj(Args... args)
    {
        std::unique_lock l(mutex_);
        STATS_EVENT_NEW();
        if (!free_) {
            alloc_batch(batch_);
        }
        FreeNode *const ptr = free_;
        free_ = ptr->next_;
        ptr->~FreeNode();
        return ::new (std::launder(ptr)) T(args...);
    }

    void delete_obj(T *obj)
    {
        obj->~T();
        FreeNode *const ptr = ::new (std::launder(obj)) FreeNode;
        std::unique_lock l(mutex_);
        STATS_EVENT_DELETE();
        ptr->next_ = free_;
        free_ = ptr;
    }

private:
    void alloc_batch(size_t batch)
    {
        for (size_t i = 0; i < batch; ++i) {
            Space *const sp = new Space;
            sp->~Space();
            FreeNode *const ptr = ::new (std::launder(sp)) FreeNode;
            ptr->next_ = free_;
            free_ = ptr;
        }
        STATS_EVENT_ALLOC(batch);
    }

    void free_all()
    {
        FreeNode *ptr = free_;
        while (ptr) {
            FreeNode *const next = ptr->next_;
            ptr->~FreeNode();
            Space *const sp = ::new (std::launder(ptr)) Space;
            delete sp;
            ptr = next;
        }
    }

/// STATS
#undef STATS_EVENT_ALLOC
#undef STATS_EVENT_DELETE
#undef STATS_EVENT_NEW

public:
    std::string print_stats()
    {
        std::string str;
#ifdef MONAD_BATCH_MEM_POOL_STATS
        str += stats_.print_stats();
        if constexpr (std::same_as<Mutex, SpinLock>) {
            str += " " + mutex_.print_stats();
        }
        stats_.clear_stats();
#endif
        return str;
    }

private:
#ifdef MONAD_BATCH_MEM_POOL_STATS
    /// PoolStats
    struct PoolStats
    {
        /// DATA
        uint64_t n_alloc_{0};
        uint64_t n_new_{0};
        uint64_t n_delete_{0};

        /// MEMBER FUNCTIONS
        void event_alloc(size_t batch)
        {
            n_alloc_ += batch;
        }

        void event_new()
        {
            ++n_new_;
        }

        void event_delete()
        {
            ++n_delete_;
        }

        std::string print_stats()
        {
            char str[100];
            sprintf(str, "%3ld %5ld %5ld", n_alloc_, n_new_, n_delete_);
            return std::string(str);
        }

        void clear_stats()
        {
            n_alloc_ = 0;
            n_new_ = 0;
            n_delete_ = 0;
        }
    }; /// PoolStats

    PoolStats stats_;
#endif // MONAD_BATCH_MEM_POOL_STATS

}; /// BatchMemPool

MONAD_NAMESPACE_END
