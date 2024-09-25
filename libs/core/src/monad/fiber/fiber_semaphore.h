#pragma once

/**
 * @file
 *
 * This file implements a semaphore object used with monad_fiber
 */

#include <stddef.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/core/spinloop.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_fiber_semaphore monad_fiber_semaphore_t;

/// Initialize a semaphore
static void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem);

/// Acquire a wakeup token from the semaphore; this operation is conventionally
/// called "wait" (or 'P') in the literature because, if a wakeup token is not
/// available immediately, the caller will sleep
static void monad_fiber_semaphore_acquire(
    monad_fiber_semaphore_t *sem, monad_fiber_prio_t wakeup_prio);

/// A non-blocking form of acquire; the wakeup token will be consumed if
/// available, and the return value will indicate what happened
static bool monad_fiber_semaphore_try_acquire(monad_fiber_semaphore_t *sem);

/// Acquire a wakeup token from a semaphore when the calling context is a
/// regular thread, not a fiber; see fiber-api.md for more details about this
/// function and how it should be used
static inline void
monad_fiber_semaphore_thread_acquire_one(monad_fiber_semaphore_t *sem);

/// Release the given number of wakeup tokens, potentially waking up waiting
/// fibers if there are any; this operation is also conventionally called
/// "signal" (or 'V')
static void monad_fiber_semaphore_release(
    monad_fiber_semaphore_t *sem, unsigned num_tokens);

// clang-format off

struct monad_fiber_semaphore
{
    alignas(64) monad_spinlock_t lock;     ///< Protects all members
    void *user_data;                       ///< Opaque user data
    monad_fiber_wait_queue_t fiber_queue;  ///< List of waiting fibers
    unsigned tokens;                       ///< Immediate wakeup tokens
};

// clang-format on

inline void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem)
{
    monad_spinlock_init(&sem->lock);
    sem->user_data = nullptr;
    TAILQ_INIT(&sem->fiber_queue);
    sem->tokens = 0;
}

inline void monad_fiber_semaphore_acquire(
    monad_fiber_semaphore_t *sem, monad_fiber_prio_t wakeup_prio)
{
    monad_fiber_t *self = nullptr;

TryAgain:
    MONAD_SPINLOCK_LOCK(&sem->lock);
    if (MONAD_UNLIKELY(sem->tokens == 0)) {
        // No token available; sleep on this semaphore and suspend our fiber.
        // We'll be resumed later when someone else calls the release routine,
        // which will reschedule us to become runnable again
        if (MONAD_LIKELY(self == nullptr)) {
            self = monad_fiber_self();
            MONAD_DEBUG_ASSERT(self != nullptr); // Running on ordinary thread?
        }
        else {
            // See comment in monad_fiber_channel_pop
            ++self->stats.total_spurious_wakeups;
        }
        TAILQ_INSERT_TAIL(&sem->fiber_queue, self, wait_link);
        MONAD_SPINLOCK_UNLOCK(&sem->lock);
        _monad_fiber_sleep(self, wakeup_prio, sem);
        goto TryAgain;
    }
    // Take a wakeup token and return
    --sem->tokens;
    MONAD_SPINLOCK_UNLOCK(&sem->lock);
}

inline bool monad_fiber_semaphore_try_acquire(monad_fiber_semaphore_t *sem)
{
    bool has_token = false;
    MONAD_SPINLOCK_LOCK(&sem->lock);
    if (MONAD_LIKELY(sem->tokens > 0)) {
        --sem->tokens;
        has_token = true;
    }
    MONAD_SPINLOCK_UNLOCK(&sem->lock);
    return has_token;
}

inline void
monad_fiber_semaphore_thread_acquire_one(monad_fiber_semaphore_t *sem)
{
    unsigned expected;
    MONAD_DEBUG_ASSERT(monad_fiber_self() == nullptr);
TryAgain:
    expected = 1;
    if (MONAD_UNLIKELY(!__atomic_compare_exchange_n(
            &sem->tokens,
            &expected,
            0,
            true,
            __ATOMIC_ACQ_REL,
            __ATOMIC_RELAXED))) {
        monad_spinloop_hint();
        goto TryAgain;
    }
}

inline void
monad_fiber_semaphore_release(monad_fiber_semaphore_t *sem, unsigned num_tokens)
{
    monad_fiber_t *waiter;

    if (MONAD_UNLIKELY(num_tokens == 0)) {
        // Explicitly checking for zero makes the structure of the loop a
        // little cleaner given the protocol around acquiring and releasing
        // `sem->lock`
        return;
    }
    do {
        MONAD_SPINLOCK_LOCK(&sem->lock);
        waiter = TAILQ_FIRST(&sem->fiber_queue);
        if (waiter == nullptr) {
            // There are no fibers waiting to wakeup; store the remaining
            // wakeup tokens and exit
            sem->tokens += num_tokens;
            MONAD_SPINLOCK_UNLOCK(&sem->lock);
            break;
        }

        // There is at least one waiting fiber; try to wake it up
        ++sem->tokens;
        --num_tokens;
        TAILQ_REMOVE(&sem->fiber_queue, waiter, wait_link);
        MONAD_SPINLOCK_UNLOCK(&sem->lock);
        while (!_monad_fiber_try_wakeup(waiter))
            ;
    }
    while (num_tokens > 0);
}

#ifdef __cplusplus
} // extern "C"
#endif
