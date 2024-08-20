#pragma once

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinloop.h>
#include <monad/core/tl_tid.h>

#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    #include <monad/core/srcloc.h>
#endif

#include <assert.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#ifdef __cplusplus
    #include <new>
#endif

static_assert(ATOMIC_INT_LOCK_FREE == 2);

typedef struct monad_spinlock monad_spinlock_t;

#if MONAD_SPINLOCK_TRACK_STATS
    #if MONAD_SPINLOCK_TRACK_STATS_ATOMIC
        typedef atomic_ulong monad_spinstat_t;
        #define MONAD_SPINSTAT_INC(X)                                          \
            atomic_fetch_add_explicit(&(X), 1, memory_order_relaxed)
    #else
        typedef unsigned long monad_spinstat_t;
        #define MONAD_SPINSTAT_INC(X) ++(X)
    #endif
#else
    typedef unsigned long monad_spinstat_t;
    #define MONAD_SPINSTAT_INC(X)
#endif

#define MONAD_SPINLOCK_HIST_BUCKETS 15

// clang-format off
/// Lock statistics; these may not be 100% accurate, since we may not be
/// atomically incrementing them (some data could be lost)
struct monad_spinlock_stats
{
    monad_spinstat_t total_try_locks;      ///< # times try_lock is called
    monad_spinstat_t total_try_lock_fail;  ///< # times try_lock failed
    monad_spinstat_t total_locks;          ///< # times lock is called
    monad_spinstat_t total_lock_init_fail; ///< # times lock needed > 1 try
    monad_spinstat_t
        tries_histogram[MONAD_SPINLOCK_HIST_BUCKETS + 1]; /// lock tries histo
};

// clang-format on

struct monad_spinlock
{
    atomic_int owner_tid; ///< System ID of thread that owns lock
#if MONAD_SPINLOCK_TRACK_STATS
    struct monad_spinlock_stats stats; ///< Lock contention stats
#endif
#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    monad_source_location_t srcloc; ///< Location in code where lock taken
#endif
};

static inline bool monad_spinlock_is_self_owned(monad_spinlock_t *const lock)
{
    return atomic_load_explicit(&lock->owner_tid, memory_order_acquire) ==
           get_tl_tid();
}

static inline bool monad_spinlock_is_unowned(monad_spinlock_t *const lock)
{
    return atomic_load_explicit(&lock->owner_tid, memory_order_acquire) == 0;
}

static inline void monad_spinlock_init(monad_spinlock_t *const lock)
{
    lock->owner_tid = 0;
#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    memset(&lock->srcloc, 0, sizeof lock->srcloc);
#endif
#if MONAD_SPINLOCK_TRACK_STATS
    #ifdef __cplusplus
    new (&lock->stats) monad_spinlock_stats{};
    #else
    memset(&lock->stats, 0, sizeof lock->stats);
    #endif
#endif
}

static inline bool monad_spinlock_try_lock(monad_spinlock_t *const lock)
{
    int expected = 0;
    MONAD_SPINSTAT_INC(lock->stats.total_try_locks);
    bool const is_locked = atomic_compare_exchange_strong_explicit(
        &lock->owner_tid,
        &expected,
        get_tl_tid(),
        memory_order_acq_rel,
        memory_order_relaxed);
    if (MONAD_UNLIKELY(!is_locked)) {
        MONAD_SPINSTAT_INC(lock->stats.total_try_lock_fail);
    }
    return is_locked;
}

static inline void monad_spinlock_lock(monad_spinlock_t *const lock)
{
    MONAD_SPINSTAT_INC(lock->stats.total_locks);
    int const desired = get_tl_tid();
    int expected;
    bool owned;
    [[maybe_unused]] unsigned long tries = 0;
    [[maybe_unused]] unsigned histo_bucket;

    MONAD_DEBUG_ASSERT(!monad_spinlock_is_self_owned(lock));

TryAgain:
    expected = 0;
    owned = atomic_compare_exchange_weak_explicit(
        &lock->owner_tid,
        &expected,
        desired,
        memory_order_acq_rel,
        memory_order_relaxed);
    if (MONAD_UNLIKELY(!owned)) {
        monad_spinloop_hint();
#if MONAD_SPINLOCK_TRACK_STATS
        ++tries;
#endif
        goto TryAgain;
    }

#if MONAD_SPINLOCK_TRACK_STATS
    if (MONAD_LIKELY(tries > 1)) {
        MONAD_SPINSTAT_INC(lock->stats.total_lock_init_fail);
    }
    histo_bucket = stdc_bit_width(tries - 1);
    if (MONAD_UNLIKELY(histo_bucket >= MONAD_SPINLOCK_HIST_BUCKETS)) {
        histo_bucket = MONAD_SPINLOCK_HIST_BUCKETS;
    }
    MONAD_SPINSTAT_INC(lock->stats.tries_histogram[histo_bucket]);
#endif
}

static inline void monad_spinlock_unlock(monad_spinlock_t *const lock)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(lock));
    atomic_store_explicit(&lock->owner_tid, 0, memory_order_release);
}

#if MONAD_SPINLOCK_TRACK_OWNER_INFO
static inline bool monad_spinlock_try_lock_with_srcloc(
    monad_spinlock_t *const lock, monad_source_location_t srcloc)
{
    bool const have_lock = monad_spinlock_try_lock(lock);
    if (have_lock) {
        lock->srcloc = srcloc;
    }
    return have_lock;
}

static inline void monad_spinlock_lock_with_srcloc(
    monad_spinlock_t *const lock, monad_source_location_t srcloc)
{
    monad_spinlock_lock(lock);
    lock->srcloc = srcloc;
}

    #define MONAD_SPINLOCK_TRY_LOCK(LCK)                                       \
        monad_spinlock_try_lock_with_srcloc(                                   \
            (LCK), MONAD_SOURCE_LOCATION_CURRENT())

    #define MONAD_SPINLOCK_LOCK(LCK)                                           \
        monad_spinlock_lock_with_srcloc((LCK), MONAD_SOURCE_LOCATION_CURRENT())
#else

    #define MONAD_SPINLOCK_TRY_LOCK(LCK) monad_spinlock_try_lock((LCK))
    #define MONAD_SPINLOCK_LOCK(LCK) monad_spinlock_lock((LCK))

#endif

#define MONAD_SPINLOCK_UNLOCK(LCK) monad_spinlock_unlock((LCK))
