#pragma once

#include <errno.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdio.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/mem/cma/cma_alloc.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_run_queue_stats;
typedef struct monad_run_queue monad_run_queue_t;

/// Create a fiber run queue of the specified fixed size; this is a priority
/// queue of fibers, ordered by the monad_fiber_t scheduling "priority" field
int monad_run_queue_create(
    monad_allocator_t *alloc, size_t capacity, monad_run_queue_t **rq);

/// Destroys a fiber run queue; destruction is not thread safe, so all push and
/// pop operations must be finished
void monad_run_queue_destroy(monad_run_queue_t *rq);

/// Try to push a fiber onto the priority queue; this is non-blocking and
/// returns ENOBUFS immediately is there is insufficient space in the queue
static int
monad_run_queue_try_push(monad_run_queue_t *rq, monad_fiber_t *fiber);

/// Try to pop the highest priority fiber from the queue; this is non-blocking
/// and returns nullptr if the queue is empty, otherwise it returns a locked
/// fiber
static monad_fiber_t *monad_run_queue_try_pop(monad_run_queue_t *rq);

/// Returns true if the run queue is currently empty; be aware that this has
/// a TOCTOU race in multithreaded code, e.g., this could change asynchronously
/// because of another thread
static bool monad_run_queue_is_empty(monad_run_queue_t const *rq);

// clang-format off

/// Scheduling statistics; some writes to these are unlocked without the use
/// of fetch_add atomic semantics, so they are only approximate
struct monad_run_queue_stats
{
    size_t total_pop;            ///< # of times caller tried to pop a fiber
    size_t total_pop_empty;      ///< # of times there was no fiber in queue
    size_t total_push;           ///< # of times caller tried to push a fiber
    size_t total_push_full;      ///< # of times fiber queue was full
    size_t total_push_not_ready; ///< # of times pushed fiber unready
    size_t *heapify_iter_histogram; ///< Histogram of heapify iterations
    monad_memblk_t histogram_blk;   ///< Allocator handle for histo memory
};

// clang-format on

/// A priority queue, implemented using a min-heap; used to pick the highest
/// priority fiber to schedule next. For reference, see
/// [CLRS 6.5: Priority Queues]
struct monad_run_queue
{
    alignas(64) monad_spinlock_t lock;
    monad_fiber_t **fibers;
    size_t capacity;
    monad_allocator_t *alloc;
    monad_memblk_t self_memblk;
    alignas(64) atomic_size_t size;
    uint64_t serial_id;
    alignas(64) struct monad_run_queue_stats stats;
};

#define PQ_PARENT_IDX(i) ((i - 1) / 2)
#define PQ_LEFT_CHILD_IDX(i) (2 * i + 1)
#define PQ_RIGHT_CHILD_IDX(i) (2 * i + 2)

#if MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO
    #define PQ_IS_HIGHER_PRIO(L, R) ((L)->rq_priority < (R)->rq_priority)
#else
    #define PQ_IS_HIGHER_PRIO(L, R) ((L)->priority < (R)->priority)
#endif

// Same as monad_run_queue_try_push, but as a global (non-inlinable) symbol;
// this is needed to work around a circular dependency, because the inlinable
// code in run_queue.h and fiber_impl.h both want to call each other
extern int
_monad_run_queue_try_push_global(monad_run_queue_t *rq, monad_fiber_t *fiber);

static inline void
_monad_fiber_ptr_swap(monad_fiber_t const **p1, monad_fiber_t const **p2)
{
    monad_fiber_t const *const t = *p2;
    *p2 = *p1;
    *p1 = t;
}

static inline unsigned prio_queue_min_heapify(
    monad_fiber_t const **fibers, size_t queue_size, size_t parent_idx)
{
    unsigned iters = 1;
HeapifyNextLevel:
    size_t highest_prio_idx = parent_idx;
    size_t left_idx = PQ_LEFT_CHILD_IDX(parent_idx);
    size_t right_idx = PQ_RIGHT_CHILD_IDX(parent_idx);

    if (left_idx < queue_size &&
        PQ_IS_HIGHER_PRIO(fibers[left_idx], fibers[highest_prio_idx])) {
        highest_prio_idx = left_idx;
    }

    if (right_idx < queue_size &&
        PQ_IS_HIGHER_PRIO(fibers[right_idx], fibers[highest_prio_idx])) {
        highest_prio_idx = right_idx;
    }

    if (highest_prio_idx == parent_idx) {
        return iters;
    }

    _monad_fiber_ptr_swap(&fibers[parent_idx], &fibers[highest_prio_idx]);
    parent_idx = highest_prio_idx;
    ++iters;
    goto HeapifyNextLevel;
}

inline int monad_run_queue_try_push(monad_run_queue_t *rq, monad_fiber_t *fiber)
{
    size_t idx;
    size_t size;
    int rc = 0;
    unsigned heapify_iters = 0;

    MONAD_DEBUG_ASSERT(rq != nullptr && fiber != nullptr);
    MONAD_SPINLOCK_LOCK(&rq->lock);
    ++rq->stats.total_push;
    // Relaxed because it isn't ordered before the spinlock acquisition
    size = atomic_load_explicit(&rq->size, memory_order_relaxed);
    if (MONAD_UNLIKELY(size == rq->capacity)) {
        ++rq->stats.total_push_full;
        rc = ENOBUFS;
        goto Finish;
    }

    if (MONAD_UNLIKELY(!monad_spinlock_is_self_owned(&fiber->lock))) {
        MONAD_SPINLOCK_LOCK(&fiber->lock);
    }
    switch (fiber->state) {
    case MF_STATE_INIT:
        [[fallthrough]];
    case MF_STATE_FINISHED:
        rc = ENXIO;
        ++rq->stats.total_push_not_ready;
        goto Finish;

    case MF_STATE_WAIT_QUEUE:
        fiber->wait_object = nullptr;
        [[fallthrough]];
    case MF_STATE_CAN_RUN:
        rc = 0;
        break;

    default:
        rc = EBUSY;
        ++rq->stats.total_push_not_ready;
        goto Finish;
    }

    idx = size++;
#if MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO
    // To robustly support fibers with equal priority, we need to adjust the
    // scheduling priority so that reinsertion effectively lowers the priority,
    // see the comment in the run_queue.equal_round_robin unit test
    fiber->rq_priority =
        ((__int128_t)fiber->priority << 64) | (rq->serial_id++);
#endif
    rq->fibers[idx] = fiber;
    while (idx != 0 &&
           PQ_IS_HIGHER_PRIO(rq->fibers[idx], rq->fibers[PQ_PARENT_IDX(idx)])) {
        _monad_fiber_ptr_swap(
            (monad_fiber_t const **)&rq->fibers[idx],
            (monad_fiber_t const **)&rq->fibers[PQ_PARENT_IDX(idx)]);
        idx = PQ_PARENT_IDX(idx);
        ++heapify_iters;
    }
    fiber->run_queue = rq;
    fiber->state = MF_STATE_RUN_QUEUE;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    atomic_store_explicit(&rq->size, size, memory_order_relaxed);
    ++rq->stats.heapify_iter_histogram[stdc_bit_width(heapify_iters)];
Finish:
    MONAD_SPINLOCK_UNLOCK(&rq->lock);
    return rc;
}

inline monad_fiber_t *monad_run_queue_try_pop(monad_run_queue_t *rq)
{
    monad_fiber_t *min_prio_fiber;
    size_t size;
    unsigned heapify_iter;

    MONAD_DEBUG_ASSERT(rq != nullptr);
    ++rq->stats.total_pop;
    // Because we're I/O bound, the run_queue is usually empty (we're often
    // waiting for any fiber to become runnable again). To prevent constant lock
    // contention, the queue size is atomic and we can poll it
    size = atomic_load_explicit(&rq->size, memory_order_acquire);
    if (MONAD_UNLIKELY(size == 0)) {
        ++rq->stats.total_pop_empty;
        return nullptr;
    }
    if (MONAD_UNLIKELY(!MONAD_SPINLOCK_TRY_LOCK(&rq->lock))) {
        ++rq->stats.total_pop_empty;
        // We failed to get the lock; the likeliest sequence of events is that
        // we had multiple pollers and only one fiber became available. By
        // failing to get the lock, we likely would fail completely (the size
        // will probably be zero soon)
        return nullptr;
    }
    // The size may have changed in between our polling of the size and getting
    // the lock that protects writes to it; the load is relaxed here since we
    // piggy-back off the memory ordering imposed by the spinlock
    size = atomic_load_explicit(&rq->size, memory_order_relaxed);
    if (MONAD_UNLIKELY(size == 0)) {
        ++rq->stats.total_pop_empty;
        MONAD_SPINLOCK_UNLOCK(&rq->lock);
        return nullptr;
    }

    min_prio_fiber = rq->fibers[0];

#if MONAD_CORE_RUN_QUEUE_NO_MIGRATE
    if (min_prio_fiber->last_thread != 0 &&
        min_prio_fiber->last_thread != pthread_self()) {
        MONAD_SPINLOCK_UNLOCK(&rq->lock);
        return nullptr;
    }
#endif

    --size;
    atomic_store_explicit(&rq->size, size, memory_order_release);
    if (MONAD_LIKELY(size > 0)) {
        _monad_fiber_ptr_swap(
            (monad_fiber_t const **)&rq->fibers[0],
            (monad_fiber_t const **)&rq->fibers[size]);
        heapify_iter =
            prio_queue_min_heapify((monad_fiber_t const **)rq->fibers, size, 0);
        ++rq->stats.heapify_iter_histogram[stdc_bit_width(heapify_iter)];
    }
    MONAD_SPINLOCK_UNLOCK(&rq->lock);

    // Return the fiber in a locked state; the caller is almost certainly going
    // to call monad_fiber_run immediately
    MONAD_SPINLOCK_LOCK(&min_prio_fiber->lock);
    min_prio_fiber->state = MF_STATE_CAN_RUN;
    return min_prio_fiber;
}

inline bool monad_run_queue_is_empty(monad_run_queue_t const *rq)
{
    return atomic_load_explicit(&rq->size, memory_order_relaxed) == 0;
}

#undef PQ_PARENT_IDX
#undef PQ_LEFT_CHILD_IDX
#undef PQ_RIGHT_CHILD_IDX
#undef PQ_IS_HIGHER_PRIO

#ifdef __cplusplus
} // extern "C"
#endif
