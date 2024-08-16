#pragma once

#include "task.h"

#include <monad/linked_list_impl_common.h>

#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct io_buffer_awaiting_list_item_t
{
    struct io_buffer_awaiting_list_item_t *prev, *next;
};
struct monad_async_executor_impl;

struct monad_async_task_impl
{
    struct monad_async_task_head head;
    char magic[8];
    struct monad_async_task_impl *prev, *next;
    monad_context context;
    bool please_cancel_invoked;
    monad_c_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task);

    struct
    {
        monad_async_io_status *front, *back;
        size_t count;
    } io_submitted, io_completed;

    struct io_buffer_awaiting_list_item_t io_buffer_awaiting;
    bool io_buffer_awaiting_was_inserted_at_front;
    bool io_buffer_awaiting_is_for_write;
    bool io_buffer_awaiting_is_for_large_page;

    monad_async_io_status **completed;

    /* Set this to have it executed next time executor run regains control at:

    - After task has exited and been fully detached from its executor.
    */
    monad_c_result (*call_after_suspend_to_executor)(
        struct monad_async_task_impl *task);
    void *call_after_suspend_to_executor_data;
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_async_task_impl) == 304);
static_assert(
    sizeof(struct monad_async_task_impl) <= MONAD_CONTEXT_TASK_ALLOCATION_SIZE);
    #ifdef __cplusplus
static_assert(alignof(struct monad_async_task_impl) == 8);
    #endif
#endif

static inline monad_async_priority monad_async_task_effective_cpu_priority(
    const struct monad_async_task_impl *task)
{
    return task->io_buffer_awaiting_was_inserted_at_front
               ? monad_async_priority_high
               : task->head.priority.cpu;
}

#ifdef __cplusplus
}
#endif
