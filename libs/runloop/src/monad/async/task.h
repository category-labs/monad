#pragma once

#include "../context/context_switcher.h"

#include <liburing.h>

// Must come after <liburing.h>, otherwise breaks build on clang
#include <monad/util/ticks_count.h>

#include <stdatomic.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C"
{
#endif
typedef struct monad_async_executor_head *monad_async_executor;

typedef struct monad_async_task_head *monad_async_task;

struct monad_fiber_task;
struct monad_fiber_scheduler;

//! \brief Task priority classes
typedef enum monad_async_priority
    : unsigned char
{
    monad_async_priority_high = 0,
    monad_async_priority_normal = 1,
    monad_async_priority_low = 2,

    monad_async_priority_max = 3,
    monad_async_priority_unchanged = (unsigned char)-1
} monad_async_priority;

#if defined(__clang__)
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wgnu-anonymous-struct"
    #pragma clang diagnostic ignored "-Wnested-anon-types"
#elif defined(__GNUC__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wpedantic"
#endif

//! \brief An i/o status state used to identify an i/o in progress. Must NOT
//! move in memory until the operation completes.
typedef struct monad_async_io_status
{
    struct monad_async_io_status *MONAD_CONTEXT_PUBLIC_CONST prev,
        *MONAD_CONTEXT_PUBLIC_CONST next;
    monad_c_result (*MONAD_CONTEXT_PUBLIC_CONST cancel_)(
        monad_async_task, struct monad_async_io_status *, bool);

    union
    {
        //! Unspecified value immediately after initiating call returns. Will
        //! become bytes transferred if operation is successful, or another
        //! error if it fails or is cancelled.
        MONAD_CONTEXT_PUBLIC_CONST monad_c_result result;

        struct
        {
            monad_async_task task_;
            struct monad_async_task_registered_io_buffer *tofill_;
            void *file_or_sock_;
        };
    };

    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_initiated;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_completed;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_reaped;

#ifdef __cplusplus
    constexpr monad_async_io_status()
        : prev{}
        , next{}
        , cancel_{}
        , result{}
        , ticks_when_initiated{}
        , ticks_when_completed{}
        , ticks_when_reaped{}
    {
    }
#endif

    // You can place any additional data you want after here ...
} monad_async_io_status;

#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(monad_async_io_status) == 80);
    #ifdef __cplusplus
static_assert(alignof(monad_async_io_status) == 8);
    #endif
#endif

#if defined(__clang__)
    #pragma clang diagnostic pop
#elif defined(__GNUC__)
    #pragma GCC diagnostic pop
#endif

//! \brief True if the i/o is currently in progress
static inline bool
monad_async_is_io_in_progress(monad_async_io_status const *iostatus)
{
    return iostatus->ticks_when_completed == 1;
}

//! \brief Number of the i/o is currently in progress
static inline size_t
monad_async_io_in_progress(monad_async_io_status const *iostatus, size_t len)
{
    size_t ret = 0;
    for (size_t n = 0; n < len; n++) {
        if (monad_async_is_io_in_progress(&iostatus[n])) {
            ret++;
        }
    }
    return ret;
}

//! \brief The public attributes of a task
struct monad_async_task_head
{
    struct monad_context_task_head derived;

    // Set this to have i/o completions target a different task to this
    // one. This can be useful where you have tasks work on what i/o to
    // initiate, but a different task will reap i/o completions.
    struct monad_async_task_head *io_recipient_task
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    // The following are **NOT** user modifiable
    MONAD_CONTEXT_PUBLIC_CONST struct
    {
        monad_async_priority cpu MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
        monad_async_priority io MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    } priority;

    // All of these next refer to the i/o executor only i.e. if running on a
    // foreign executor, is_running will be false as that is not the i/o
    // executor.
    MONAD_CONTEXT_PUBLIC_CONST
    MONAD_CPP_ATOMIC(monad_async_executor)
    current_executor MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST MONAD_CPP_ATOMIC(bool)
        is_awaiting_dispatch MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_pending_launch MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_running MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_suspended_for_io MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        // Note that is_suspended_sqe_exhaustion and
        // is_suspended_sqe_exhaustion_wr are their own wait lists and
        // is_suspended_awaiting will be false
        is_suspended_sqe_exhaustion MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_suspended_sqe_exhaustion_wr MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        // Note is_suspended_io_buffer_exhaustion uses the is_suspended_awaiting
        // and is_suspended_completed wait lists so one of those will be true
        // as well
        is_suspended_io_buffer_exhaustion MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        // Note is_suspended_max_concurrency uses the is_suspended_awaiting
        // and is_suspended_completed wait lists so one of those will be true
        // as well
        is_suspended_max_concurrency MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_suspended_awaiting MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        is_suspended_completed MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_submitted
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_attached
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_detached
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t
        ticks_when_suspended_awaiting MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t
        ticks_when_suspended_completed MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t ticks_when_resumed
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    MONAD_CONTEXT_PUBLIC_CONST monad_cpu_ticks_count_t total_ticks_executed
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    MONAD_CONTEXT_PUBLIC_CONST unsigned io_submitted
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE,
        io_completed_not_reaped MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_async_task_head) == 168);
    #ifdef __cplusplus
static_assert(alignof(struct monad_async_task_head) == 8);
    #endif
#endif

//! \brief True if the task has completed executing and has exited
static inline bool monad_async_task_has_exited(monad_async_task const task)
{
#ifdef __cplusplus
    return task->is_awaiting_dispatch.load(std::memory_order_acquire) ==
               false &&
           task->current_executor.load(std::memory_order_acquire) == nullptr;
#else
    return atomic_load_explicit(
               &task->is_awaiting_dispatch, memory_order_acquire) == false &&
           atomic_load_explicit(
               &task->current_executor, memory_order_acquire) == NULL;
#endif
}

//! \brief If the i/o is currently in progress, returns the task which initiated
//! the i/o. Otherwise returns nullptr.
static inline monad_async_task
monad_async_io_status_owning_task(monad_async_io_status const *iostatus)
{
    if (!monad_async_is_io_in_progress(iostatus)) {
        return NULL;
    }

    union punner
    {
        monad_c_result res;
        monad_async_task task;
    } pun;

    pun.res = iostatus->result;
    return pun.task;
}

//! \brief Attributes by which to construct a task
struct monad_async_task_attr
{
    struct monad_context_task_attr derived;
};

//! \brief EXPENSIVE Creates a task instance using the specified context
//! switcher.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_create(
    monad_async_task *task, monad_context_switcher switcher,
    struct monad_async_task_attr *attr);

//! \brief EXPENSIVE Destroys a task instance. If the task is currently
//! suspended, it will be cancelled first in which case `EAGAIN` may be returned
//! from this function until cancellation succeeds.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_destroy(monad_async_task task);

//! \brief Check that the task's metadata matches the lists it is in etc.
extern void monad_async_task_debug_validate(monad_async_task task);

/*! \brief Initiate the transfer of a task's context's execution to a different
type of executor.

This function suspends the execution of the task and requests its executor to
optionally take a copy of the public information of the task into `opt_save` so
it can be restored later (this preserves tick counts etc), detach the task from
the executor, and then invoke the supplied function with the now 'naked' task.
Another type of executor may then overwrite the bytes after `monad_context_task`
up to `MONAD_CONTEXT_TASK_ALLOCATION_SIZE`. If you need to pass your `to_invoke`
additional state, remember there is a `user_ptr` in `monad_context_task`.

Remember that when the context resumes execution in the new executor, anything
related to `monad_async_*` no longer applies. You can choose the return value of
this function by setting `task->head.derived.result` before resuming the
context.

If your context wishes to return to this executor later, consider using
`monad_async_task_from_foreign_context()` followed by
`monad_async_task_attach()`.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_suspend_save_detach_and_invoke(
    monad_async_task task, monad_async_task opt_save,
    monad_c_result (*to_invoke)(monad_context_task detached_task));

//! \brief Optionally copies the `monad_async_*` parts of `opt_save` into
//! `context_task`, and returns it as a `monad_async_task`.
extern monad_async_task monad_async_task_from_foreign_context(
    monad_context_task context_task, monad_async_task opt_save);

//! \brief THREADSAFE Attaches a task instance onto a given executor, which
//! means it will launch the next time the executor runs. If the task is
//! attached already to a different executor, you MUST call this function from
//! that executor's kernel thread. If you optionally choose to reparent the
//! task's context to a new context switcher instance (typical if attaching
//! to an executor on a different kernel thread), it MUST be the same type of
//! context switcher.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_attach(
    monad_async_executor executor, monad_async_task task,
    monad_context_switcher opt_reparent_switcher); // implemented in executor.c

//! \brief THREADSAFE If a task is currently suspended on an operation, cancel
//! it. This can take some time for the relevant io_uring operation to also
//! cancel. If the task is yet to launch, don't launch it. If the task isn't
//! currently running, do nothing. The suspension point will return
//! `ECANCELED` next time the cancelled task resumes.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_cancel(
    monad_async_executor executor,
    monad_async_task task); // implemented in executor.c

//! \brief Change the CPU or i/o priority of a task
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_set_priorities(
    monad_async_task task, monad_async_priority cpu,
    monad_async_priority io); // implemented in executor.c

//! \brief Ask io_uring to cancel a previously initiated operation. It can take
//! some time for io_uring to cancel an operation, and it may ignore your
//! request.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_io_cancel(
    monad_async_task task,
    monad_async_io_status *iostatus); // implemented in executor.c

//! \brief Iterate through completed i/o for this task, reaping each from the
//! completed but not reaped list.
BOOST_OUTCOME_C_NODISCARD extern monad_async_io_status *
monad_async_task_completed_io(
    monad_async_task task); // implemented in executor.c

//! \brief Non-cancellable infinity duration
static uint64_t const monad_async_duration_infinite_non_cancelling =
    (uint64_t)-1;

//! \brief Cancellable infinity duration
static uint64_t const monad_async_duration_infinite_cancelling =
    31536000000000000ULL; // ten years

/*! \brief OPTIONAL CANCELLATION POINT Suspend execution of a task for a given
duration, which can be zero (which equates "yield"). If `completed` is not
null, if any i/o which the task has initiated completes during the
suspension, resume the task setting `completed` to which i/o has just
completed. This i/o is NOT REAPED, you must separately call
`monad_async_task_completed_io()` to reap that i/o.

If `ns` is the special duration `monad_async_duration_infinite_non_cancelling`,
that makes this function (and all those based upon it) not a cancellation
point. This lets you tear down any initiated i/o etc before exiting your task.
If you want infinity but it should be a cancellation point, use
`monad_async_duration_infinite_cancelling`.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_suspend_for_duration(
    monad_async_io_status **completed, monad_async_task task,
    uint64_t ns); // implemented in executor.c

//! \brief CANCELLATION POINT Combines `monad_async_task_completed_io()` and
//! `monad_async_task_suspend_for_duration()` to conveniently reap completed
//! i/o, suspending the task until more i/o completes. Returns zero when no more
//! i/o, otherwise returns i/o initiated plus i/o completed not reaped including
//! i/o returned i.e. how much i/o work remains before the task, and when it
//! becomes zero there is none remaining.
static inline monad_c_result monad_async_task_suspend_until_completed_io(
    monad_async_io_status **completed, monad_async_task task, uint64_t ns)
{
    *completed = monad_async_task_completed_io(task);
    if (*completed != NULL) {
        return monad_c_make_success(
            (intptr_t)task->io_submitted +
            (intptr_t)task->io_completed_not_reaped + 1);
    }
    if (task->io_submitted == 0) {
        return monad_c_make_success(0);
    }
    monad_c_result r =
        monad_async_task_suspend_for_duration(completed, task, ns);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        return r;
    }
    *completed = monad_async_task_completed_io(task);
    return monad_c_make_success(
        (intptr_t)task->io_submitted + (intptr_t)task->io_completed_not_reaped +
        (*completed != NULL));
}

//! \brief A registered i/o buffer
typedef struct monad_async_task_registered_io_buffer
{
    int index;
    struct iovec iov[1];
} monad_async_task_registered_io_buffer;

//! \brief Flags for claiming a registered i/o buffer
struct monad_async_task_claim_registered_io_buffer_flags
{
    //! \brief If there aren't enough buffers, return `ENOMEM` instead of
    //! suspending until more buffers appear. An error is always returned if no
    //! buffers were configured.
    unsigned fail_dont_suspend : 1;

    // internal use only
    unsigned _for_read_ring : 1;
};

/*! \brief CANCELLATION POINT Claim an unused registered **write** buffer for
file i/o, suspending if none currently available unless the `fail_dont_suspend`
flag is set.

There are two sizes of registered i/o write buffer, small and large which are
the page size of the host platform (e.g. 4Kb and 2Mb if on Intel x64). Through
being always whole page sizes, DMA using registered i/o buffers has the lowest
possible overhead.

It is important to note that these buffers can ONLY be used for write operations
on the write ring. For read operations, it is io_uring which allocates the
buffers.

Because it is you the user who claims write buffers, it is on you to detect
and avoid write buffer deadlock where that might occur. Generally, you should
allocate more write buffers than extant write i/o could ever occur, but if
that isn't feasible then you ought to set the `fail_dont_suspend` flag and
then either schedule the write i/o for later, or use a non-registered buffer,
or some other strategy. The error returned will be equivalent to `ENOBUFS`.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_claim_registered_file_io_write_buffer(
    monad_async_task_registered_io_buffer *buffer, monad_async_task task,
    size_t bytes_requested,
    struct monad_async_task_claim_registered_io_buffer_flags
        flags); // implemented in executor.c

/*! \brief CANCELLATION POINT Claim an unused registered **write** buffer for
socket i/o, suspending if none currently available unless the
`fail_dont_suspend` flag is set.

There are two sizes of registered i/o write buffer, small and large which are
the page size of the host platform (e.g. 4Kb and 2Mb if on Intel x64). Through
being always whole page sizes, DMA using registered i/o buffers has the lowest
possible overhead.

It is important to note that these buffers can ONLY be used for write operations
on the write ring. For read operations, it is io_uring which allocates the
buffers.

Because it is you the user who claims write buffers, it is on you to detect
and avoid write buffer deadlock where that might occur. Generally, you should
allocate more buffers than extant i/o could ever occur (as for socket i/o, read
and write buffers come from the same pool), but if that isn't feasible then you
ought to set the `fail_dont_suspend` flag and then either schedule the write i/o
for later, or use a non-registered buffer, or some other strategy. The error
returned will be equivalent to `ENOBUFS`.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_claim_registered_socket_io_write_buffer(
    monad_async_task_registered_io_buffer *buffer, monad_async_task task,
    size_t bytes_requested,
    struct monad_async_task_claim_registered_io_buffer_flags
        flags); // implemented in executor.c

/*! \brief Release a previously claimed registered buffer.

You must claim write i/o buffers using
`monad_async_task_claim_registered_file_io_write_buffer()` or
`monad_async_task_claim_registered_socket_io_write_buffer()`. Read i/o buffers
are allocated by io_uring, you release them after use using this function.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_release_registered_io_buffer(
    monad_async_task task, int buffer_index); // implemented in executor.c

#ifdef __cplusplus
}
#endif
