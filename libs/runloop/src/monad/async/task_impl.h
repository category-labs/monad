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

struct max_concurrent_io_list_item_t
{
    struct max_concurrent_io_list_item_t *prev, *next;
};
struct monad_async_executor_impl;

enum monad_async_task_impl_please_cancel_invoked_status : uint8_t
{
    please_cancel_not_invoked = 0,
    please_cancel_invoked_not_seen_yet,
    please_cancel_invoked_seen,
    please_cancel_invoked_seen_awaiting_uring, // io_uring still has to return a
                                               // completion
    please_cancel_cancelled
};

struct monad_async_task_impl
{
    struct monad_async_task_head head;
    char magic[8];
    struct monad_async_task_impl *prev, *next;
    monad_c_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task);

    // For io_uring ops which use monad_async_io_status as their base
    struct
    {
        monad_async_io_status *front, *back;
        size_t count;
    } io_submitted, io_completed;

    union
    {
        struct io_buffer_awaiting_list_item_t io_buffer_awaiting;
        struct max_concurrent_io_list_item_t max_concurrent_io_awaiting;
    };

    monad_async_io_status **completed;
    bool io_buffer_awaiting_was_inserted_at_front;
    bool io_buffer_awaiting_is_for_write;
    bool io_buffer_awaiting_is_for_large_page;
    enum monad_async_task_impl_please_cancel_invoked_status
        please_cancel_status;
    int8_t please_cancel_invoked_suspending_ops_remaining;

    /* Set this to have it executed next time executor run regains control
    at:

    - After task has exited and been fully detached from its executor.
    */
    monad_c_result (*call_after_suspend_to_executor)(monad_context_task task);
    void *call_after_suspend_to_executor_data;
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(
    sizeof(struct monad_async_task_impl) == MONAD_ASYNC_TASK_FOOTPRINT);
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
