#pragma once

#include "executor.h"

#include <stdatomic.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The public attributes of a work dispatcher
typedef struct monad_async_work_dispatcher_head
{
    // The following are not user modifiable
#ifdef __cplusplus
    // C++ is difficult here and requires std::
    MONAD_ASYNC_PUBLIC_CONST struct
    {
        std::atomic_uint working, idle;
    } executors;

    std::atomic_size_t tasks_awaiting_dispatch;
#else
    MONAD_ASYNC_PUBLIC_CONST struct
    {
        atomic_uint working, idle;
    } executors;

    MONAD_ASYNC_PUBLIC_CONST atomic_size_t tasks_awaiting_dispatch;
#endif
} *monad_async_work_dispatcher;

//! \brief The public attributes of a work dispatcher
typedef struct monad_async_work_dispatcher_executor_head
{
    // The following are not user modifiable
    struct monad_async_executor_head *const derived;
    struct monad_async_work_dispatcher_head *MONAD_ASYNC_PUBLIC_CONST
        dispatcher;
    MONAD_ASYNC_PUBLIC_CONST
#ifdef __cplusplus
    std::
#endif
        atomic_bool is_working,
        is_idle;
} *monad_async_work_dispatcher_executor;

//! \brief Attributes by which to construct a work dispatcher
struct monad_async_work_dispatcher_attr
{
    //! Dispatcher executors should spin the CPU for this many milliseconds
    //! before sleeping
    uint32_t spin_before_sleep_ms;
};

//! \brief Attributes by which to construct a work dispatcher
struct monad_async_work_dispatcher_executor_attr
{
    struct monad_async_executor_attr derived;
};

//! \brief EXPENSIVE Creates a work dispatcher instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_create(
    monad_async_work_dispatcher *dp,
    struct monad_async_work_dispatcher_attr *attr);

//! \brief EXPENSIVE Destroys a work dispatcher instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_destroy(monad_async_work_dispatcher dp);

//! \brief EXPENSIVE Creates a work dispatcher executor instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_executor_create(
    monad_async_work_dispatcher_executor *ex, monad_async_work_dispatcher dp,
    struct monad_async_work_dispatcher_executor_attr *attr);

//! \brief EXPENSIVE Destroys a work dispatcher executor instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_executor_destroy(
    monad_async_work_dispatcher_executor ex);

//! \brief Calls `monad_async_executor_run()` for the calling kernel thread,
//! attaching tasks recently submitted to kernel threads in the pool with spare
//! capacity as per the work dispatcher's configured policy. Returns the number
//! of work items executed, or -1 when time to exit.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_executor_run(
    monad_async_work_dispatcher_executor ex);

//! \brief THREADSAFE Causes a sleeping work dispatcher executor to wake. Same
//! as `monad_async_executor_wake()`, but for work dispatcher executors.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_executor_wake(
    monad_async_work_dispatcher_executor ex,
    monad_async_result const *cause_run_to_return);

//! \brief THREADSAFE Submits one or more tasks to be executed by the first
//! available executor within the work dispatcher pool. Higher priority tasks
//! are executed before lower priority tasks.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_submit(
    monad_async_work_dispatcher dp, monad_async_task *tasks, size_t count);

//! \brief THREADSAFE Wait until all work has been dispatched or executed.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_wait(
    monad_async_work_dispatcher dp, size_t max_undispatched,
    size_t max_unexecuted, struct timespec *timeout);

//! \brief THREADSAFE Tells executors to quit, preferring idle executors first,
//! until no more than `max_executors` remains.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_work_dispatcher_quit(
    monad_async_work_dispatcher dp, size_t max_executors,
    struct timespec *timeout);

#ifdef __cplusplus
}
#endif
