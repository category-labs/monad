#include <errno.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

int monad_run_queue_create(
    monad_allocator_t *alloc, size_t capacity, monad_run_queue_t **rq)
{
    static_assert(alignof(monad_run_queue_t) >= alignof(monad_run_queue_t *));
    monad_run_queue_t *run_queue;
    monad_memblk_t memblk;
    int rc;
    size_t const total_size =
        sizeof *run_queue + capacity * sizeof(monad_fiber_t *);
    if (rq == nullptr) {
        return EFAULT;
    }
    rc =
        monad_cma_alloc(alloc, total_size, alignof(monad_run_queue_t), &memblk);
    if (rc != 0) {
        return rc;
    }
    *rq = run_queue = memblk.ptr;
    memset(run_queue, 0, sizeof *run_queue);
    monad_spinlock_init(&run_queue->lock);
    run_queue->fibers = (monad_fiber_t **)(run_queue + 1);
    run_queue->capacity = capacity;
    run_queue->alloc = alloc;
    run_queue->self_memblk = memblk;
    run_queue->size = 0;
    rc = monad_cma_calloc(
        alloc,
        stdc_bit_width(capacity),
        sizeof(size_t),
        alignof(size_t),
        &run_queue->stats.histogram_blk);
    ;
    if (rc != 0) {
        monad_run_queue_destroy(run_queue);
        return rc;
    }
    run_queue->stats.heapify_iter_histogram =
        run_queue->stats.histogram_blk.ptr;
    memset(
        run_queue->stats.heapify_iter_histogram,
        0,
        sizeof(size_t) * stdc_bit_width(capacity));
    return 0;
}

void monad_run_queue_destroy(monad_run_queue_t *rq)
{
    MONAD_ASSERT(rq != nullptr);
    if (rq->stats.histogram_blk.ptr) {
        monad_cma_dealloc(rq->alloc, rq->stats.histogram_blk);
    }
    monad_cma_dealloc(rq->alloc, rq->self_memblk);
}

int _monad_run_queue_try_push_global(
    monad_run_queue_t *rq, monad_fiber_t *fiber)
{
    return monad_run_queue_try_push(rq, fiber);
}
