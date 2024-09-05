#pragma once

#include <monad/core/cpu_relax.h>
#include <monad/core/likely.h>
#include <monad/core/thread.h>

#include <assert.h>
#include <stdatomic.h>
#include <stdbool.h>

static_assert(ATOMIC_LONG_LOCK_FREE == 2);

typedef atomic_long spinlock_t;

static inline void spinlock_init(spinlock_t *const lock)
{
    atomic_init(lock, 0);
}

static inline bool spinlock_try_lock(spinlock_t *const lock)
{
    monad_tid_t expected = 0;
    monad_tid_t const desired = monad_thread_get_id();
    return atomic_compare_exchange_weak_explicit(
        lock, &expected, desired, memory_order_acquire, memory_order_relaxed);
}

static inline void spinlock_lock(spinlock_t *const lock)
{
    monad_tid_t const desired = monad_thread_get_id();
    for (;;) {
        /**
         * TODO further analysis of retry logic
         * - if weak cmpxch fails, spin again or cpu relax?
         * - compare intel vs arm
         * - benchmark with real use cases
         */
        unsigned retries = 0;
        while (
            MONAD_UNLIKELY(atomic_load_explicit(lock, memory_order_relaxed))) {
            if (MONAD_LIKELY(retries < 128)) {
                ++retries;
            }
            else {
                cpu_relax();
            }
        }
        monad_tid_t expected = 0;
        if (MONAD_LIKELY(atomic_compare_exchange_weak_explicit(
                lock,
                &expected,
                desired,
                memory_order_acquire,
                memory_order_relaxed))) {
            break;
        }
    }
}

static inline void spinlock_unlock(spinlock_t *const lock)
{
    atomic_store_explicit(lock, 0, memory_order_release);
}
