#pragma once

#include <category/core/synchronization/spin_lock.hpp>

#include <boost/pool/pool.hpp>

#include <concepts>
#include <mutex>
#include <new>
#include <string>
#include <utility>

MONAD_NAMESPACE_BEGIN

/// Memory pool for objects of type 'T' that supports preallocation
/// and batch allocation. It grows but does not shrink. Memory is
/// deallocated at the destruction of the pool.

template <class T>
class BatchMemPool
{
    /// TYPES
    using Mutex = SpinLock;

    using Pool = boost::pool<>;

    /// DATA
    Mutex mutex_{};
    Pool pool_;

/// STATS MACROS
#ifdef MONAD_BATCH_MEM_POOL_STATS
    #define STATS_EVENT_DELETE() stats_.event_delete()
    #define STATS_EVENT_NEW() stats_.event_new()
#else
    #define STATS_EVENT_DELETE()
    #define STATS_EVENT_NEW()
#endif

public:
    BatchMemPool(size_t const initial, size_t const batch = 1024)
        : pool_{sizeof(T), initial}
    {
        void *p = pool_.malloc();
        pool_.free(p);
        p = nullptr;
        pool_.set_next_size(batch);
        pool_.set_max_size(batch);
    }

    template <class... Args>
    T *new_obj(Args &&...args)
    {
        void *p = nullptr;
        {
            std::lock_guard const l{mutex_};
            STATS_EVENT_NEW();
            p = pool_.malloc();
        }
        if (MONAD_LIKELY(p)) {
            T *result = static_cast<T *>(p);
            try {
                new (result) T(std::forward<Args>(args)...);
            }
            catch (...) {
                std::lock_guard const l{mutex_};
                pool_.free(p);
                throw;
            }
            return result;
        }
        throw std::bad_alloc{};
    }

    void delete_obj(T *const obj)
    {
        obj->~T();
        std::lock_guard const l{mutex_};
        STATS_EVENT_DELETE();
        pool_.free(obj);
    }

private:
/// STATS
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
        uint64_t n_new_{0};
        uint64_t n_delete_{0};

        /// MEMBER FUNCTIONS
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
            sprintf(str, "%5ld %5ld", n_new_, n_delete_);
            return std::string(str);
        }

        void clear_stats()
        {
            n_new_ = 0;
            n_delete_ = 0;
        }
    }; /// PoolStats

    PoolStats stats_;
#endif // MONAD_BATCH_MEM_POOL_STATS

}; /// BatchMemPool

MONAD_NAMESPACE_END
