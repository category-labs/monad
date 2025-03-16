#pragma once

/**
 * @file
 *
 * This file implements the "channels" concurrent programming abstraction for
 * monad_fiber objects.
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/queue.h>
#include <sys/uio.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_fiber_channel monad_fiber_channel_t;
typedef struct monad_fiber_msghdr monad_fiber_msghdr_t;

/// Initialize a channel
static void monad_fiber_channel_init(monad_fiber_channel_t *channel);

/// Push a message onto a channel; if a fiber is waiting for a message because
/// of a previous call to `monad_fiber_channel_pop`, that fiber will be
/// rescheduled to run as a result of this call
static void monad_fiber_channel_push(
    monad_fiber_channel_t *channel, monad_fiber_msghdr_t *msghdr);

/// Try to pop a message from the channel; "try" means that this is a
/// non-blocking call: if nothing is available, nullptr is returned immediately
static monad_fiber_msghdr_t *
monad_fiber_channel_try_pop(monad_fiber_channel_t *channel);

/// Pop a message from the channel; this may sleep if no messages are available;
/// if we are put to sleep, we will be rescheduled with the given wakeup
/// priority
static monad_fiber_msghdr_t *monad_fiber_channel_pop(
    monad_fiber_channel_t *channel, monad_fiber_prio_t wakeup_prio);

/// Initialize a message header whose content buffer is described by the given
/// `struct iovec` memory area
static void
monad_fiber_msghdr_init(monad_fiber_msghdr_t *m, struct iovec const iov);

/// Initialize a message whose content memory area defined is defined by
/// [(uint8_t const*)(m + 1), ((uint8_t const*)(m + 1) + trailing_size)
static void
monad_fiber_msghdr_init_trailing(monad_fiber_msghdr_t *m, size_t trailing_size);

/// Descriptor for a message enqueued on a channel; see the fiber-api.md
/// documentation section on memory management for an explanation of this
/// object
struct monad_fiber_msghdr
{
    TAILQ_ENTRY(monad_fiber_msghdr) link; ///< Linkage to next msghdr in list
    struct iovec msg_buf; ///< Buffer storing message payload
};

// clang-format off

struct monad_fiber_channel
{
    alignas(64) monad_spinlock_t lock;           ///< Protects all members
    void *user_data;                             ///< Opaque user data
    monad_fiber_wait_queue_t fiber_queue;        ///< List of waiting fibers
    TAILQ_HEAD(, monad_fiber_msghdr) ready_msgs; ///< List of ready messages
};

// clang-format on

inline void monad_fiber_channel_init(monad_fiber_channel_t *channel)
{
    monad_spinlock_init(&channel->lock);
    channel->user_data = nullptr;
    TAILQ_INIT(&channel->fiber_queue);
    TAILQ_INIT(&channel->ready_msgs);
}

inline void monad_fiber_channel_push(
    monad_fiber_channel_t *channel, monad_fiber_msghdr_t *m)
{
    monad_fiber_t *waiter;

    MONAD_SPINLOCK_LOCK(&channel->lock);
    // Insert the message into the ready queue; if a fiber is ready to wake up,
    // it will pull it from here upon wakeup
    TAILQ_INSERT_TAIL(&channel->ready_msgs, m, link);
    waiter = TAILQ_FIRST(&channel->fiber_queue);
    if (waiter == nullptr) {
        // There are no fibers ready to wake up; we're done
        MONAD_SPINLOCK_UNLOCK(&channel->lock);
        return;
    }

    // There is at least one fiber waiting for a value; try forever to wake it
    // up
    TAILQ_REMOVE(&channel->fiber_queue, waiter, wait_link);
    MONAD_SPINLOCK_UNLOCK(&channel->lock);
    while (!_monad_fiber_try_wakeup(waiter))
        ;
}

inline monad_fiber_msghdr_t *
monad_fiber_channel_try_pop(monad_fiber_channel_t *channel)
{
    monad_fiber_msghdr_t *msghdr = nullptr;
    MONAD_SPINLOCK_LOCK(&channel->lock);
    if (MONAD_LIKELY(!TAILQ_EMPTY(&channel->ready_msgs))) {
        msghdr = TAILQ_FIRST(&channel->ready_msgs);
        TAILQ_REMOVE(&channel->ready_msgs, msghdr, link);
    }
    MONAD_SPINLOCK_UNLOCK(&channel->lock);
    return msghdr;
}

inline monad_fiber_msghdr_t *monad_fiber_channel_pop(
    monad_fiber_channel_t *channel, monad_fiber_prio_t wakeup_prio)
{
    monad_fiber_msghdr_t *msghdr;
    monad_fiber_t *self = nullptr;

TryAgain:
    MONAD_SPINLOCK_LOCK(&channel->lock);
    msghdr = TAILQ_FIRST(&channel->ready_msgs);
    if (MONAD_UNLIKELY(msghdr == nullptr)) {
        // No value is ready; sleep on this channel and suspend our fiber.
        // We'll be resumed later when someone else calls the push routine,
        // which will reschedule us to become runnable again
        if (MONAD_LIKELY(self == nullptr)) {
            self = monad_fiber_self();
            MONAD_DEBUG_ASSERT(self != nullptr); // Running on ordinary thread?
        }
        else {
            // We've been through this path once already. This means we were
            // woken up to take a message, but didn't wake up fast enough and
            // someone else took it first while the lock was dropped. Now we
            // need to sleep again. Note that `self` is not locked here, but
            // it's OK: no one else should touch the stats cache line while
            // the state is MF_STATE_WAIT_QUEUE
            ++self->stats.total_spurious_wakeups;
        }
        TAILQ_INSERT_TAIL(&channel->fiber_queue, self, wait_link);
        MONAD_SPINLOCK_UNLOCK(&channel->lock);
        _monad_fiber_sleep(self, wakeup_prio, channel);
        goto TryAgain;
    }

    // A message is ready immediately; hand it back
    TAILQ_REMOVE(&channel->ready_msgs, msghdr, link);
    MONAD_SPINLOCK_UNLOCK(&channel->lock);
    return msghdr;
}

inline void
monad_fiber_msghdr_init(monad_fiber_msghdr_t *m, struct iovec const iov)
{
    MONAD_DEBUG_ASSERT(m != nullptr);
    memset(m, 0, sizeof *m);
    m->msg_buf = iov;
}

inline void
monad_fiber_msghdr_init_trailing(monad_fiber_msghdr_t *m, size_t trailing_size)
{
    struct iovec const iov = {.iov_base = m + 1, .iov_len = trailing_size};
    monad_fiber_msghdr_init(m, iov);
}

#ifdef __cplusplus
} // extern "C"
#endif
