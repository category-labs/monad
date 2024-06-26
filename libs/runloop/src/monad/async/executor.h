#pragma once

#include "config.h"

#include <liburing.h>

// Must come after <liburing.h>, otherwise breaks build on clang
#include <stdatomic.h>

#include "task.h"

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The public attributes of an executor
typedef struct monad_async_executor_head
{
    // The following are not user modifiable
#ifdef __cplusplus
    // C++ is difficult here and requires std::
    std::atomic<monad_async_task> current_task;
    std::atomic_size_t tasks_pending_launch;
    std::atomic_size_t tasks_running;
    std::atomic_size_t tasks_suspended_sqe_exhaustion;
    std::atomic_size_t tasks_suspended;
#else
    _Atomic monad_async_task current_task;
    atomic_size_t tasks_pending_launch;
    atomic_size_t tasks_running;
    atomic_size_t tasks_suspended_sqe_exhaustion;
    atomic_size_t tasks_suspended;
#endif
    monad_async_cpu_ticks_count_t total_ticks_in_run;
    monad_async_cpu_ticks_count_t total_ticks_in_task_launch;
    monad_async_cpu_ticks_count_t total_ticks_in_io_uring;
    monad_async_cpu_ticks_count_t total_ticks_sleeping;
    monad_async_cpu_ticks_count_t total_ticks_in_task_completion;
} *monad_async_executor;

//! \brief Returns true if an executor has work before it
static inline bool monad_async_executor_has_work(monad_async_executor ex)
{
#ifdef __cplusplus
    return ex->current_task.load(std::memory_order_acquire) != nullptr ||
           ex->tasks_pending_launch.load(std::memory_order_acquire) > 0 ||
           ex->tasks_running.load(std::memory_order_acquire) > 0 ||
           ex->tasks_suspended_sqe_exhaustion.load(std::memory_order_acquire) >
               0 ||
           ex->tasks_suspended.load(std::memory_order_acquire) > 0;
#else
    return atomic_load_explicit(&ex->current_task, memory_order_acquire) !=
               NULL ||
           atomic_load_explicit(
               &ex->tasks_pending_launch, memory_order_acquire) > 0 ||
           atomic_load_explicit(&ex->tasks_running, memory_order_acquire) > 0 ||
           atomic_load_explicit(
               &ex->tasks_suspended_sqe_exhaustion, memory_order_acquire) > 0 ||
           atomic_load_explicit(&ex->tasks_suspended, memory_order_acquire) > 0;
#endif
}

//! \brief Attributes by which to construct an executor
struct monad_async_executor_attr
{
    struct
    {
        //! \brief If this is zero, this executor will be incapable of doing
        //! i/o! It also no longer initialises io_uring for this executor.
        unsigned entries;
        struct io_uring_params params;

        struct
        {
            //! \brief How many small and large buffers to register.
            unsigned small_count, large_count;
            //! \brief How many of each of small pages and of large pages the
            //! small and large buffer sizes are.
            unsigned small_multiplier, large_multiplier;
        } registered_buffers;
    } io_uring_ring, io_uring_wr_ring;
};

/*! \brief EXPENSIVE Creates an executor instance. You must create it on the
 kernel thread where it will be used.

Generally, one also needs to create context switcher instances for each
executor instance. This is because the context switcher needs to store how
to resume the executor when a task's execution suspends.

You can optionally create an io_uring instance for the executor by setting
`attr->io_uring_ring.entries` to non-zero. This will then be used to dispatch
work instead of an internal dispatcher.

You may additionally optionally create a second io_uring instance called
"write ring" by setting `attr->io_uring_wr_ring.entries` to non-zero. This
is mandatory if you wish to write to files, otherwise it is not used.

The reason a special io_uring instance is used for operations which modify
files is because a total sequentially consistent order is applied to all file
write operations. This implements a "multi-copy atomic" memory model similar
to that used by ARM microprocessors. This is a weak memory model, but one
sufficient to prevent:

1. Write amplification on the device caused by multiple concurrent writes.

2. Writes appearing to readers not in the order of write submission.

The most efficient way of implementing this weak memory model is a specially
configured io_uring instance, so this is why we have that.

Do NOT use the "write ring" for writes to sockets, it will severely impact
performance!
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_create(
    monad_async_executor *ex, struct monad_async_executor_attr *attr);

//! \brief EXPENSIVE Destroys an executor instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_executor_destroy(monad_async_executor ex);

/*! \brief Processes no more than `max_items` work items, returning the number
of items processed. A null `timeout` means wait forever, and a zero timeout will
poll without blocking.

Note that this function is particularly prone to early return i.e. partly
or entirely ignoring timeout. Causes can include being woken externally by
`monad_async_executor_wake()`, there being write i/o pending (as then two
rings need to be checked), and the usual spurious early timeouts from Linux.
If you do complex processing around calling this function, it may be wise
to only do that processing if the value returned is not zero.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_run(
    monad_async_executor ex, size_t max_items, struct timespec *timeout);

//! \brief THREADSAFE Causes a sleeping executor to wake. Can be called from any
//! kernel thread. `cause_run_to_return` causes `monad_async_executor_run()` to
//! return the result given, otherwise the internal sleep wakes, executor state
//! is examined for new work and the sleep reestablished WHICH MAY NOT CAUSE RUN
//! TO RETURN.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_wake(
    monad_async_executor ex, monad_async_result const *cause_run_to_return);

#ifdef __cplusplus
}
#endif
