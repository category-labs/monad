#pragma once

#if defined(__cplusplus)
extern "C"
{
#endif

#include <stddef.h>
#include <stdint.h>

typedef struct monad_fiber_task
{
    void (*resume)(struct monad_fiber_task *const);
    void (*destroy)(struct monad_fiber_task *const);

    int64_t priority;
} monad_fiber_task_t;

typedef struct monad_fiber_task_queue
{

    // ring buffer. not lock free.
    monad_fiber_task_t **memory;
    size_t capacity;
    monad_fiber_task_t **data;
    size_t size;
} monad_fiber_task_queue_t;

void monad_fiber_task_queue_init(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_destroy(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_grow(struct monad_fiber_task_queue *);
monad_fiber_task_t *
monad_fiber_task_queue_pop_front(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_insert(
    struct monad_fiber_task_queue *, monad_fiber_task_t *task);

#if defined(__cplusplus)
}
#endif
