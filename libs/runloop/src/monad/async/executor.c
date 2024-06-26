#include "executor.h"

#include "boost_result.h"
#include "config.h"
#include "context_switcher.h"
#include "task.h"

#include "executor_impl.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include <liburing.h>
#include <poll.h>
#include <sys/mman.h>

#if MONAD_ASYNC_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif

// This is not a fast call, and should be avoided where possible
static inline bool is_address_dereferenceable(void *addr)
{
#if MONAD_ASYNC_HAVE_ASAN
    return !__asan_address_is_poisoned(addr);
#else
    void *toprobe = (void *)((uintptr_t)addr & ~(uintptr_t)4095u);
    void *mapaddr = mmap(
        toprobe,
        4096,
        PROT_NONE,
        MAP_ANONYMOUS | MAP_PRIVATE | MAP_NORESERVE | MAP_FIXED_NOREPLACE,
        -1,
        0);
    if (mapaddr != MAP_FAILED) {
        munmap(mapaddr, 4096);
        if (mapaddr == toprobe) {
            return false;
        }
    }
    return true;
#endif
}

monad_async_result monad_async_executor_create(
    monad_async_executor *ex, struct monad_async_executor_attr *attr)
{
    struct monad_async_executor_impl *p =
        (struct monad_async_executor_impl *)calloc(
            1, sizeof(struct monad_async_executor_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    MONAD_ASYNC_TRY_RESULT(
        (void)monad_async_executor_destroy((monad_async_executor)p),
        monad_async_executor_create_impl(p, attr));
    *ex = (monad_async_executor)p;
    return monad_async_make_success(0);
}

monad_async_result monad_async_executor_destroy(monad_async_executor ex_)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    MONAD_ASYNC_TRY_RESULT(, monad_async_executor_destroy_impl(ex));
    free(ex);
    return monad_async_make_success(0);
}

struct launch_pending_tasks_state
{
    struct monad_async_executor_impl *ex;
    size_t const *max_items;

    size_t items;
    LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
    size_t tasks_pending_launch_count;
    monad_async_priority current_priority;
};

static inline monad_async_result monad_async_executor_impl_launch_pending_tasks(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct launch_pending_tasks_state *state =
        (struct launch_pending_tasks_state *)user_ptr;
    for (; state->current_priority < monad_async_priority_max;
         state->current_priority++) {
        while (state->tasks_pending_launch[state->current_priority].count > 0) {
            if (++state->items > *state->max_items) {
                goto exit;
            }
            struct monad_async_task_impl *task =
                state->tasks_pending_launch[state->current_priority].front;
            LIST_REMOVE(
                state->tasks_pending_launch[state->current_priority],
                task,
                &state->tasks_pending_launch_count);
            LIST_APPEND_ATOMIC_COUNTER(
                state->ex->tasks_running[task->head.priority.cpu],
                task,
                &state->ex->head.tasks_running);
            atomic_store_explicit(
                &task->head.is_running, true, memory_order_release);
            atomic_store_explicit(
                &task->head.is_pending_launch, false, memory_order_release);
            task->head.ticks_when_resumed =
                get_ticks_count(memory_order_relaxed);
            atomic_store_explicit(
                &state->ex->head.current_task,
                &task->head,
                memory_order_release);
            // This may suspend, in which case we shall either resume above
            // or it wil return (depends on context switch implementation)
            atomic_load_explicit(&task->context->switcher, memory_order_acquire)
                ->resume(fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has launched %zu pending tasks\n",
        (void *)state->ex,
        state->items);
#endif
    return monad_async_make_success(0);
}

struct resume_tasks_state
{
    struct monad_async_executor_impl *ex;
    size_t const *global_max_items, local_max_items;
    struct list_define_p_monad_async_task_impl_t *wait_list;

    size_t items;
    monad_async_priority current_priority;
};

static inline monad_async_result monad_async_executor_impl_resume_tasks(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct resume_tasks_state *state = (struct resume_tasks_state *)user_ptr;
    for (; state->current_priority < monad_async_priority_max;
         state->current_priority++) {
        struct list_define_p_monad_async_task_impl_t *wait_list =
            &state->wait_list[state->current_priority];
        while (wait_list->count > 0) {
            if (state->items >= *state->global_max_items ||
                state->items >= state->local_max_items) {
                goto exit;
            }
            ++state->items;
            // Resume execution of the task. If it suspends on
            // another operation, or exits, the loop will resume
            // iterating above or return here
            struct monad_async_task_impl *task = wait_list->front;
            atomic_load_explicit(&task->context->switcher, memory_order_acquire)
                ->resume(fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has notified %zu tasks of i/o completion "
        "by resumption\n",
        (void *)state->ex,
        state->items);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_run_impl(
    struct monad_async_executor_impl *ex, size_t max_items,
    struct timespec *timeout_)
{
    struct timespec *timeout = timeout_;
    struct launch_pending_tasks_state launch_pending_tasks_state = {
        .ex = ex, .max_items = &max_items};
    bool timed_out = false;
    bool retry_after_this = false;
    do {
        timed_out = false;
        retry_after_this = false;
        monad_async_cpu_ticks_count_t const launch_begin =
            get_ticks_count(memory_order_relaxed);
        if (atomic_load_explicit(
                &ex->need_to_empty_eventfd, memory_order_acquire) ||
            atomic_load_explicit(
                &ex->head.tasks_pending_launch, memory_order_acquire) > 0) {
            atomic_lock(&ex->lock);
            for (bool done = false; !done;) {
                done = true;
                if (ex->tasks_pending_launch.count > 0) {
                    struct monad_async_task_impl *const task =
                        ex->tasks_pending_launch.front;
                    LIST_REMOVE_ATOMIC_COUNTER(
                        ex->tasks_pending_launch,
                        task,
                        &ex->head.tasks_pending_launch);
                    LIST_APPEND(
                        launch_pending_tasks_state
                            .tasks_pending_launch[task->head.priority.cpu],
                        task,
                        &launch_pending_tasks_state.tasks_pending_launch_count);
                    done = false;
                    if (launch_pending_tasks_state.tasks_pending_launch_count >=
                        max_items) {
                        done = true;
                        break;
                    }
                }
            }
            if (atomic_load_explicit(
                    &ex->need_to_empty_eventfd, memory_order_acquire)) {
                eventfd_t v;
                if (-1 == eventfd_read(ex->eventfd, &v)) {
                    atomic_unlock(&ex->lock);
                    return monad_async_make_failure(errno);
                }
                atomic_store_explicit(
                    &ex->need_to_empty_eventfd, false, memory_order_release);
            }
            atomic_unlock(&ex->lock);
        }
        struct timespec no_waiting = {.tv_sec = 0, .tv_nsec = 0};
        struct timespec single_millisecond_waiting = {
            .tv_sec = 0, .tv_nsec = 1000000};
        if (atomic_load_explicit(
                &ex->head.tasks_suspended, memory_order_acquire) > 0) {
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                if (ex->tasks_suspended_completed[n].count > 0) {
                    timeout = &no_waiting;
                    break;
                }
            }
        }
        if (launch_pending_tasks_state.tasks_pending_launch_count > 0) {
            assert(
                launch_pending_tasks_state.tasks_pending_launch_count <=
                max_items);
            timeout = &no_waiting;
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                while (
                    max_items > 0 &&
                    launch_pending_tasks_state.tasks_pending_launch[n].count >
                        0) {
                    struct monad_async_task_impl *task =
                        launch_pending_tasks_state.tasks_pending_launch[n]
                            .front;
                    monad_async_context_switcher task_switcher =
                        atomic_load_explicit(
                            &task->context->switcher, memory_order_acquire);
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task_switcher->resume_many(
                            task_switcher,
                            monad_async_executor_impl_launch_pending_tasks,
                            &launch_pending_tasks_state));
                    if (launch_pending_tasks_state.items >= max_items) {
                        max_items = 0;
                        break;
                    }
                    else {
                        max_items -= launch_pending_tasks_state.items;
                    }
                }
            }
            // Not draining this list completely was the cause of a bug which
            // took me over a day to figure out :(
            assert(launch_pending_tasks_state.tasks_pending_launch_count == 0);
        }
        monad_async_cpu_ticks_count_t const launch_end =
            get_ticks_count(memory_order_relaxed);
        ex->head.total_ticks_in_task_launch += launch_end - launch_begin;

        if (ex->ring.ring_fd != 0) {
            monad_async_cpu_ticks_count_t const io_uring_begin =
                get_ticks_count(memory_order_relaxed);
            // Submit all enqueued ops, and wait for some completions
            struct io_uring_cqe *cqe = nullptr;
            struct io_uring *ring = nullptr;
            int r = 1;
            if (ex->wr_ring_ops_outstanding > 0) {
                ring = &ex->wr_ring;
                r = io_uring_submit(ring);
                if (r < 0) {
                    return monad_async_make_failure(-r);
                }
                while (max_items > 0 &&
                       atomic_load_explicit(
                           &ex->head.tasks_suspended_sqe_exhaustion,
                           memory_order_acquire) > 0 &&
                       io_uring_sq_space_left(&ex->wr_ring) > 0) {
                    bool done = true;
                    struct resume_tasks_state resume_tasks_state = {
                        .ex = ex,
                        .global_max_items = &max_items,
                        .local_max_items = 1,
                        .wait_list = ex->tasks_suspended_submission_wr_ring};
                    for (; resume_tasks_state.current_priority <
                           monad_async_priority_max;
                         resume_tasks_state.current_priority++) {
                        if (ex->tasks_suspended_submission_wr_ring
                                [resume_tasks_state.current_priority]
                                    .count > 0) {
                            done = false;
                            struct io_uring_sqe *sqe =
                                io_uring_get_sqe(&ex->wr_ring);
                            if (sqe == nullptr) {
                                break;
                            }
                            struct monad_async_task_impl *task =
                                ex->tasks_suspended_submission_wr_ring
                                    [resume_tasks_state.current_priority]
                                        .front;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                            printf(
                                "*** Executor %p initiates resumption of "
                                "task %p from write SQE exhaustion. "
                                "sqe=%p. sqes=%u cqes=%u.\n",
                                (void *)ex,
                                (void *)task,
                                (void *)sqe,
                                io_uring_sq_ready(&ex->wr_ring),
                                io_uring_cq_ready(&ex->wr_ring));
                            fflush(stdout);
#endif
                            monad_async_context_switcher task_switcher =
                                atomic_load_explicit(
                                    &task->context->switcher,
                                    memory_order_acquire);
                            MONAD_ASYNC_TRY_RESULT(
                                ,
                                task_switcher->resume_many(
                                    task_switcher,
                                    monad_async_executor_impl_resume_tasks,
                                    &resume_tasks_state));
                            if (resume_tasks_state.items > 0) {
                                max_items--;
                            }
                            break;
                        }
                    }
                    if (done) {
                        break;
                    }
                }
                r = io_uring_peek_cqe(ring, &cqe);
                if (timeout == nullptr || timeout != &no_waiting ||
                    timespec_to_ns(timeout) > 1000000) {
                    timeout = &single_millisecond_waiting;
                }
                if (0 == r) {
                    ex->wr_ring_ops_outstanding--;
                }
            }
            if (0 != r) {
                ring = &ex->ring;
                r = io_uring_peek_cqe(ring, &cqe);
                if (0 != r) {
                    while (max_items > 0 &&
                           atomic_load_explicit(
                               &ex->head.tasks_suspended_sqe_exhaustion,
                               memory_order_acquire) > 0 &&
                           io_uring_sq_space_left(&ex->ring) > 0) {
                        bool done = true;
                        struct resume_tasks_state resume_tasks_state = {
                            .ex = ex,
                            .global_max_items = &max_items,
                            .local_max_items = 1,
                            .wait_list = ex->tasks_suspended_submission_ring};
                        for (; resume_tasks_state.current_priority <
                               monad_async_priority_max;
                             resume_tasks_state.current_priority++) {
                            if (ex->tasks_suspended_submission_ring
                                    [resume_tasks_state.current_priority]
                                        .count > 0) {
                                done = false;
                                struct io_uring_sqe *sqe =
                                    io_uring_get_sqe(&ex->ring);
                                if (sqe == nullptr) {
                                    break;
                                }
                                struct monad_async_task_impl *task =
                                    ex->tasks_suspended_submission_ring
                                        [resume_tasks_state.current_priority]
                                            .front;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                                printf(
                                    "*** Executor %p initiates resumption of "
                                    "task %p from non-write SQE exhaustion. "
                                    "sqe=%p. sqes=%u cqes=%u.\n",
                                    (void *)ex,
                                    (void *)task,
                                    (void *)sqe,
                                    io_uring_sq_ready(&ex->ring),
                                    io_uring_cq_ready(&ex->ring));
                                fflush(stdout);
#endif
                                monad_async_context_switcher task_switcher =
                                    atomic_load_explicit(
                                        &task->context->switcher,
                                        memory_order_acquire);
                                MONAD_ASYNC_TRY_RESULT(
                                    ,
                                    task_switcher->resume_many(
                                        task_switcher,
                                        monad_async_executor_impl_resume_tasks,
                                        &resume_tasks_state));
                                if (resume_tasks_state.items > 0) {
                                    max_items--;
                                }
                                break;
                            }
                        }
                        if (done) {
                            break;
                        }
                    }
                    if (atomic_load_explicit(
                            &ex->head.tasks_suspended_sqe_exhaustion,
                            memory_order_acquire) > 0) {
                        // SQEs should get consumed quite quickly, so don't
                        // stall unblocking tasks waiting on SQEs
                        timeout = &no_waiting;
                    }
                    if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and waits forever due "
                            "to "
                            "infinite timeout. sqes=%u cqes=%u\n",
                            (void *)ex,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));
#endif
                        monad_async_cpu_ticks_count_t const sleep_begin =
                            get_ticks_count(memory_order_relaxed);
                        r = io_uring_submit_and_wait(ring, 1);
                        monad_async_cpu_ticks_count_t const sleep_end =
                            get_ticks_count(memory_order_relaxed);
                        ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                        if (r < 0) {
                            return monad_async_make_failure(-r);
                        }
                        r = io_uring_peek_cqe(ring, &cqe);
                    }
                    else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and does not wait due "
                            "to "
                            "zero "
                            "timeout. sqes=%u cqes=%u\n",
                            (void *)ex,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));

#endif
                        r = io_uring_submit(ring);
                        if (r < 0) {
                            return monad_async_make_failure(-r);
                        }
                        r = io_uring_peek_cqe(ring, &cqe);
                    }
                    else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and waits for a "
                            "non-infinite "
                            "timeout %ld-%ld. sqes=%u cqes=%u\n",
                            (void *)ex,
                            timeout->tv_sec,
                            timeout->tv_nsec,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));

#endif
                        if (ring->features & IORING_FEAT_EXT_ARG) {
                            r = io_uring_submit(ring);
                            if (r < 0) {
                                return monad_async_make_failure(-r);
                            }
                        }
                        monad_async_cpu_ticks_count_t const sleep_begin =
                            get_ticks_count(memory_order_relaxed);
                        r = io_uring_wait_cqe_timeout(
                            ring, &cqe, (struct __kernel_timespec *)timeout);
                        monad_async_cpu_ticks_count_t const sleep_end =
                            get_ticks_count(memory_order_relaxed);
                        ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                    }
                }
            }
            if (r < 0) {
                if (r == -ETIME) {
                    timed_out = true;
                }
                else if (r == -EAGAIN) {
                    // temporary failure, ignore it
                }
                else {
                    return monad_async_make_failure(-r);
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Executor %p sees cqe=%p from io_uring wait. "
                "wr_ring=%d. "
                "sqes=%u "
                "cqes=%u\n",
                (void *)ex,
                (void *)cqe,
                ring == &ex->wr_ring,
                io_uring_sq_ready(ring),
                io_uring_cq_ready(ring));
#endif
            // Always empty the completions queue irrespective of max_items
            unsigned head;
            unsigned i = 0;
            io_uring_for_each_cqe(ring, head, cqe)
            {
                i++;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** %u. Executor %p processed cqe=%p user_data=%llu "
                    "res=%d flags=%u\n",
                    i,
                    (void *)ex,
                    (void *)cqe,
                    cqe->user_data,
                    cqe->res,
                    cqe->flags);
#endif
                if (cqe->user_data == 0 && cqe->res == 0 && cqe->flags == 0) {
                    // Spurious empty CQE
                    continue;
                }
                struct monad_async_task_impl *task;
                monad_async_io_status *iostatus;
                uintptr_t magic;
                io_uring_cqe_get_data(task, iostatus, magic, cqe);
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** %u. Executor %p decodes cqe=%p into task=%p "
                    "iostatus=%p magic=%lu\n",
                    i,
                    (void *)ex,
                    (void *)cqe,
                    (void *)task,
                    (void *)iostatus,
                    magic);
                fflush(stdout);
#endif
                if (task != nullptr) {
                resume_task:
                    if (ex->cancellations_in_flight > 0) {
                        // Need to probe for spurious CQEs due to bug in Linux
                        // kernel
                        if (!is_address_dereferenceable(task) ||
                            0 != memcmp(task->magic, "MNASTASK", 8)) {
                            fprintf(
                                stderr,
                                "*** WARNING: Spurious CQE returned, "
                                "ignoring!\n");
                            continue;
                        }
                    }
                    if (atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire)) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p resumes suspended task "
                            "%p (cpu priority=%d, i/o priority=%d)\n",
                            i,
                            (void *)ex,
                            (void *)task,
                            (int)task->head.priority.cpu,
                            (int)task->head.priority.io);
#endif
                        task->head.ticks_when_suspended_completed =
                            get_ticks_count(memory_order_relaxed);
                        if (task->please_cancel_invoked) {
                            task->head.result =
                                monad_async_make_failure(ECANCELED);
                            ex->cancellations_in_flight--;
                            assert(ex->cancellations_in_flight != (unsigned)-1);
                        }
                        else if (cqe->res < 0) {
                            task->head.result =
                                monad_async_make_failure(-cqe->res);
                        }
                        else {
                            task->head.result =
                                monad_async_make_success(cqe->res);
                        }
                        atomic_store_explicit(
                            &task->head.is_suspended_awaiting,
                            false,
                            memory_order_release);
                        LIST_REMOVE(
                            ex->tasks_suspended_awaiting[task->head.priority
                                                             .cpu],
                            task,
                            (size_t *)nullptr);
                        atomic_store_explicit(
                            &task->head.is_suspended_completed,
                            true,
                            memory_order_release);
                        LIST_APPEND(
                            ex->tasks_suspended_completed[task->head.priority
                                                              .cpu],
                            task,
                            (size_t *)nullptr);
                    }
                }
                else if (iostatus != nullptr) {
                    if (ex->cancellations_in_flight > 0) {
                        // Need to probe for spurious CQEs due to bug in Linux
                        // kernel
                        if (!is_address_dereferenceable(iostatus)) {
                            fprintf(
                                stderr,
                                "*** WARNING: Spurious CQE returned, "
                                "ignoring!\n");
                            continue;
                        }
                    }
                    // result contains the pointer to the task which is to
                    // receive the i/o completion. It gets overwritten by the
                    // actual result of the i/o below, and that result will
                    // never be a valid pointer, so this check should be
                    // reliable.
                    task = *(struct monad_async_task_impl **)&iostatus->result;
                    if (ex->cancellations_in_flight > 0) {
                        if (!is_address_dereferenceable(task) ||
                            0 != memcmp(task->magic, "MNASTASK", 8)) {
                            fprintf(
                                stderr,
                                "*** WARNING: Spurious CQE returned, "
                                "ignoring!\n");
                            continue;
                        }
                    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** %u. Executor %p gets result of i/o %p "
                        "initiated "
                        "by task %p (cpu priority=%d, i/o priority=%d)\n",
                        i,
                        (void *)ex,
                        (void *)iostatus,
                        (void *)task,
                        (int)task->head.priority.cpu,
                        (int)task->head.priority.io);
                    fflush(stdout);
#endif
                    assert(task != nullptr);
                    LIST_REMOVE(
                        task->io_submitted, iostatus, &task->head.io_submitted);
                    LIST_APPEND(
                        task->io_completed,
                        iostatus,
                        &task->head.io_completed_not_reaped);
                    iostatus->cancel_ = nullptr;
                    iostatus->ticks_when_completed =
                        get_ticks_count(memory_order_relaxed);
                    if (cqe->res < 0) {
                        iostatus->result = monad_async_make_failure(-cqe->res);
                    }
                    else {
                        iostatus->result = monad_async_make_success(cqe->res);
                    }
                    if (task->completed != nullptr &&
                        atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire)) {
                        *task->completed = iostatus;
                        task->completed = nullptr;
                        cqe->res = (int)task->head.io_completed_not_reaped;
                        goto resume_task;
                    }
                }
                else if (magic == EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC) {
                    if ((cqe->flags & IORING_CQE_F_MORE) != IORING_CQE_F_MORE) {
                        // io_uring has dropped the eventfd poll
                        monad_async_result r2 =
                            monad_async_executor_setup_eventfd_polling(ex);
                        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r2)) {
                            // io_uring submit failed, if this happens something
                            // is very wrong
                            abort();
                        }
                    }
                    retry_after_this = true;
                }
                else if (magic == CANCELLED_OP_IO_URING_DATA_MAGIC) {
                    /* Used when a SQE has been retrieved but the task has
                     * been cancelled and the SQE needs to be filled with
                     * something, which will be an io_uring noop with this
                     * magic. */
                    retry_after_this = true;
                }
                else {
                    abort(); // shouldn't happen
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Executor %p has dequeued %u completions from "
                "io_uring\n",
                (void *)ex,
                i);
#endif
            io_uring_cq_advance(ring, i);
            monad_async_cpu_ticks_count_t const io_uring_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_io_uring += io_uring_end - io_uring_begin;
        }
        else {
            // If io_uring was not enabled for this executor, use the
            // eventfd as the synchronisation object
            if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits forever due to infinite "
                    "timeout\n",
                    (void *)ex);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_async_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, nullptr, nullptr);
                monad_async_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_async_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
            else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p does not wait due to zero "
                    "timeout\n",
                    (void *)ex);
#endif
            }
            else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits for a non-infinite "
                    "timeout "
                    "%ld-%ld\n",
                    (void *)ex,
                    timeout->tv_sec,
                    timeout->tv_nsec);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_async_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, timeout, nullptr);
                monad_async_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_async_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
        }
        while (ex->tasks_exited.count > 0) {
            struct monad_async_task_impl *task = ex->tasks_exited.front;
            LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
            atomic_store_explicit(
                &task->head.current_executor, nullptr, memory_order_release);
            if (task->call_after_suspend_to_executor != nullptr) {
                monad_async_result (*call_after_suspend_to_executor)(
                    struct monad_async_task_impl *task) =
                    task->call_after_suspend_to_executor;
                task->call_after_suspend_to_executor = nullptr;
                MONAD_ASYNC_TRY_RESULT(, call_after_suspend_to_executor(task));
            }
        }
        if (atomic_load_explicit(
                &ex->cause_run_to_return, memory_order_acquire) != nullptr) {
            atomic_lock(&ex->lock);
            monad_async_result r = ex->cause_run_to_return_value;
            atomic_store_explicit(
                &ex->cause_run_to_return, nullptr, memory_order_release);
            atomic_unlock(&ex->lock);
            return r;
        }
        struct resume_tasks_state resume_tasks_state = {
            .ex = ex,
            .global_max_items = &max_items,
            .local_max_items =
                ex->tasks_suspended_completed[monad_async_priority_high].count +
                ex->tasks_suspended_completed[monad_async_priority_normal]
                    .count +
                ex->tasks_suspended_completed[monad_async_priority_low].count,
            .wait_list = ex->tasks_suspended_completed};
        if (max_items > 0) {
            monad_async_cpu_ticks_count_t const completions_begin =
                get_ticks_count(memory_order_relaxed);
            for (;
                 resume_tasks_state.current_priority < monad_async_priority_max;
                 resume_tasks_state.current_priority++) {
                if (ex->tasks_suspended_completed[resume_tasks_state
                                                      .current_priority]
                        .count > 0) {
                    struct monad_async_task_impl *task =
                        ex->tasks_suspended_completed[resume_tasks_state
                                                          .current_priority]
                            .front;
                    monad_async_context_switcher task_switcher =
                        atomic_load_explicit(
                            &task->context->switcher, memory_order_acquire);
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task_switcher->resume_many(
                            task_switcher,
                            monad_async_executor_impl_resume_tasks,
                            &resume_tasks_state));
                    if (resume_tasks_state.items >= max_items) {
                        max_items = 0;
                    }
                    else {
                        max_items -= resume_tasks_state.items;
                    }
                    break;
                }
            }
            monad_async_cpu_ticks_count_t const completions_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_task_completion =
                completions_end - completions_begin;
            while (ex->tasks_exited.count > 0) {
                struct monad_async_task_impl *task = ex->tasks_exited.front;
                LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
                atomic_store_explicit(
                    &task->head.current_executor,
                    nullptr,
                    memory_order_release);
                if (task->call_after_suspend_to_executor != nullptr) {
                    monad_async_result (*call_after_suspend_to_executor)(
                        struct monad_async_task_impl *task) =
                        task->call_after_suspend_to_executor;
                    task->call_after_suspend_to_executor = nullptr;
                    MONAD_ASYNC_TRY_RESULT(
                        , call_after_suspend_to_executor(task));
                }
            }
        }
        size_t items_processed =
            launch_pending_tasks_state.items + resume_tasks_state.items;
        if (items_processed > 0) {
            return monad_async_make_success((intptr_t)items_processed);
        }
    }

    while (retry_after_this);
    return (timed_out && timeout_ != nullptr) ? monad_async_make_failure(ETIME)
                                              : monad_async_make_success(0);
}

monad_async_result monad_async_executor_run(
    monad_async_executor ex_, size_t max_items, struct timespec *timeout)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
#ifndef NDEBUG
    if (!thrd_equal(thrd_current(), ex->owning_thread)) {
        fprintf(
            stderr,
            "FATAL: You must run an executor from the same kernel "
            "thread on "
            "which it was created.\n");
        abort();
    }
#endif
    if (ex->within_run) {
        fprintf(
            stderr,
            "FATAL: You must never run an executor which is already "
            "running "
            "(i.e. recursing into the executor is forbidden).\n");
        abort();
    }
    ex->within_run = true;
    monad_async_cpu_ticks_count_t const run_begin =
        get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p enters run\n", (void *)ex);
#endif
    monad_async_result ret =
        monad_async_executor_run_impl(ex, max_items, timeout);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p exits run having processed %zu items\n",
        (void *)ex,
        ret.value);
#endif
    monad_async_cpu_ticks_count_t const run_end =
        get_ticks_count(memory_order_relaxed);
    ex->head.total_ticks_in_run += run_end - run_begin;
    ex->within_run = false;
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    return ret;
}

monad_async_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_async_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task),
    monad_async_io_status **completed)
{
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        &task->head);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task->please_cancel = please_cancel;
    task->completed = completed;
#ifndef NDEBUG
    // Trap failure to set result, EFAULT should rarely appear from a syscall
    task->head.result = monad_async_make_failure(EFAULT);
#endif
    atomic_store_explicit(&task->head.is_running, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_running[task->head.priority.cpu],
        task,
        &ex->head.tasks_running);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_suspended_awaiting[task->head.priority.cpu],
        task,
        &ex->head.tasks_suspended);
    task->head.ticks_when_suspended_awaiting =
        get_ticks_count(memory_order_relaxed);
    task->head.total_ticks_executed +=
        task->head.ticks_when_suspended_awaiting -
        task->head.ticks_when_resumed;
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p suspends task %p\n", (void *)ex, (void *)task);
#endif
    atomic_load_explicit(&task->context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(task->context, nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p resumes task %p (cpu priority=%d, i/o priority=%d)\n",
        (void *)ex,
        (void *)task,
        (int)task->head.priority.cpu,
        (int)task->head.priority.io);
#endif
    task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
    assert(!atomic_load_explicit(
        &task->head.is_suspended_awaiting, memory_order_acquire));
    assert(atomic_load_explicit(
        &task->head.is_suspended_completed, memory_order_acquire));
    atomic_store_explicit(
        &task->head.is_suspended_completed, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_suspended_completed[task->head.priority.cpu],
        task,
        &ex->head.tasks_suspended);
    atomic_store_explicit(&task->head.is_running, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_running[task->head.priority.cpu],
        task,
        &ex->head.tasks_running);
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        nullptr);
    atomic_store_explicit(
        &ex->head.current_task, &task->head, memory_order_release);
    task->please_cancel_invoked =
        false; // result of task resumption already is set
    task->please_cancel = nullptr;
    task->completed = nullptr;
    return task->head.result;
}

monad_async_result monad_async_executor_wake(
    monad_async_executor ex_, monad_async_result const *cause_run_to_return)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    atomic_lock(&ex->lock);
    monad_async_result r =
        monad_async_executor_wake_impl(&ex->lock, ex, cause_run_to_return);
    atomic_unlock(&ex->lock);
    return r;
}

void monad_async_executor_task_detach(monad_async_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (!atomic_load_explicit(
            &task_->is_running_on_foreign_executor, memory_order_acquire)) {
        assert(atomic_load_explicit(&task_->is_running, memory_order_acquire));
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task->head.current_executor, memory_order_acquire);
        assert(
            atomic_load_explicit(
                &ex->head.current_task, memory_order_acquire) == task_);
        atomic_store_explicit(
            &ex->head.current_task, nullptr, memory_order_release);
        task_->ticks_when_detached = get_ticks_count(memory_order_relaxed);
        task_->total_ticks_executed +=
            task_->ticks_when_detached - task_->ticks_when_resumed;
        atomic_store_explicit(&task_->is_running, false, memory_order_release);
        atomic_lock(&ex->lock);
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
        LIST_APPEND(ex->tasks_exited, task, (size_t *)nullptr);
        atomic_unlock(&ex->lock);
        // Reset some settings which users may have changed
        task_->io_recipient_task = task_;
        task_->priority.cpu = monad_async_priority_normal;
        task_->priority.io = monad_async_priority_normal;
    }
}

/****************************************************************************/

monad_async_result monad_async_task_attach(
    monad_async_executor ex_, monad_async_task task_,
    monad_async_context_switcher opt_reparent_switcher)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->head.user_code == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    bool const on_foreign_thread =
        !thrd_equal(thrd_current(), ex->owning_thread);
    if (atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire) != nullptr) {
#ifndef NDEBUG
        if (on_foreign_thread) {
            fprintf(
                stderr,
                "FATAL: You must detach a task on the same kernel "
                "thread on which its executor is run.\n");
            abort();
        }
#endif
        atomic_lock(&ex->lock);

        if (atomic_load_explicit(
                &task->head.is_pending_launch, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_pending_launch, task, &ex->head.tasks_pending_launch);
            atomic_store_explicit(
                &task->head.is_pending_launch, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_running, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_running[task->head.priority.cpu],
                task,
                &ex->head.tasks_running);
            atomic_store_explicit(
                &task->head.is_running, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_awaiting, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_awaiting[task->head.priority.cpu],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_awaiting, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_completed,
                     memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_completed[task->head.priority.cpu],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_completed,
                false,
                memory_order_release);
        }
        atomic_unlock(&ex->lock);
    }
    monad_async_context_switcher task_switcher =
        atomic_load_explicit(&task->context->switcher, memory_order_acquire);
    if (opt_reparent_switcher && opt_reparent_switcher != task_switcher) {
        monad_async_context_reparent_switcher(
            task->context, opt_reparent_switcher);
        task_switcher = opt_reparent_switcher;
    }
    atomic_store_explicit(
        &task->head.current_executor,
        (monad_async_executor)ex,
        memory_order_release);
    atomic_store_explicit(
        &task->head.is_pending_launch, true, memory_order_release);
    atomic_store_explicit(
        &task->head.is_awaiting_dispatch, false, memory_order_release);
    task->head.ticks_when_attached = get_ticks_count(memory_order_relaxed);
    task->head.ticks_when_detached = 0;
    task->head.ticks_when_resumed = 0;
    task->head.ticks_when_suspended_awaiting = 0;
    task->head.ticks_when_suspended_completed = 0;
    task->head.total_ticks_executed = 0;
    atomic_lock(&ex->lock);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_pending_launch, task, &ex->head.tasks_pending_launch);
    if (on_foreign_thread) {
        MONAD_ASYNC_TRY_RESULT(
            (void)atomic_unlock(&ex->lock),
            monad_async_executor_wake_impl(&ex->lock, ex, nullptr));
    }
    atomic_unlock(&ex->lock);
    return monad_async_make_success(0);
}

monad_async_result
monad_async_task_cancel(monad_async_executor ex_, monad_async_task task_)
{
    if (monad_async_task_has_exited(task_)) {
        return monad_async_make_success(0);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (atomic_load_explicit(
            &task->head.is_pending_launch, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_pending_launch, task, &ex->head.tasks_pending_launch);
        atomic_store_explicit(
            &task->head.is_pending_launch, false, memory_order_release);
        atomic_unlock(&ex->lock);
        return monad_async_make_success(0);
    }
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        fprintf(
            stderr, "TODO: Switch context back to root, and end the task\n");
        abort();
    }
    if (atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion_wr, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        task->please_cancel_invoked = true;
        // Invoke the cancellation routine
        if (task->please_cancel == nullptr) {
            atomic_unlock(&ex->lock);
            return monad_async_make_failure(EAGAIN);
        }
        monad_async_result r = task->please_cancel(ex, task);
        atomic_unlock(&ex->lock);
        return r;
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        // Have this return ECANCELED when it resumes
        task->head.result = monad_async_make_failure(ECANCELED);
        atomic_unlock(&ex->lock);
    }
    else {
        return monad_async_make_failure(ENOENT);
    }
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_set_priorities(
    monad_async_task task_, monad_async_priority cpu, monad_async_priority io)
{
    if (io != monad_async_priority_unchanged) {
        task_->priority.io = io;
    }
    if (cpu == monad_async_priority_unchanged) {
        return monad_async_make_success(0);
    }
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_awaiting, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_suspended_awaiting[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    task->head.priority.cpu = cpu;
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_awaiting, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_suspended_awaiting[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_io_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task != *(struct monad_async_task_impl **)&iostatus->result) {
        return monad_async_make_failure(ENOENT);
    }
    if (iostatus->cancel_ == nullptr) {
        return monad_async_make_failure(EAGAIN);
    }
    return iostatus->cancel_(task_, iostatus);
}

monad_async_io_status *monad_async_task_completed_io(monad_async_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    monad_async_io_status *ret = task->io_completed.front;
    if (ret == nullptr) {
        return ret;
    }
    ret->ticks_when_reaped = get_ticks_count(memory_order_relaxed);
    LIST_REMOVE(task->io_completed, ret, &task->head.io_completed_not_reaped);
    return ret;
}

static inline monad_async_result monad_async_task_suspend_for_duration_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(
        ex,
        (struct monad_async_task_impl *)atomic_load_explicit(
            &ex->head.current_task, memory_order_acquire),
        false);
    /* This is non-obvious, so it will need explaining. It turns out
    kernel 6.8 has a bug, it sometimes spuriously returns an additional CQE to
    the timeout completion CQE which most unfortunately may have a user_data
    value which was one of a previous CQE sometimes long in the past. As we
    store encoded pointers in the user data, that turns into segfaults.

    We therefore have a workaround which probes pointers returned by CQEs for
    validity but as that's very slow, we only turn it on if a cancellation is in
    flight.
    */
    ex->cancellations_in_flight++;
    io_uring_prep_timeout_remove(
        sqe, (__u64)io_uring_mangle_into_data(task), 0);
    return monad_async_make_failure(EAGAIN); // Canceller needs to wait
}

monad_async_result monad_async_task_suspend_for_duration(
    monad_async_io_status **completed, monad_async_task task_, uint64_t ns)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_invoked) {
        return monad_async_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    // timespec must live until resumption
    struct __kernel_timespec ts;
    if (ns != (uint64_t)-1 || completed == nullptr) {
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, true);
        if (sqe == nullptr) {
            assert(task->please_cancel_invoked);
            return monad_async_make_failure(ECANCELED);
        }
        if (ns == 0) {
            io_uring_prep_nop(sqe);
        }
        else {
            ts.tv_sec = (long long)(ns / 1000000000);
            ts.tv_nsec = (long long)(ns % 1000000000);
            io_uring_prep_timeout(sqe, &ts, 0, 0);
        }
        io_uring_sqe_set_data(sqe, task, task);
    }

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "suspend_for_duration ns=%lu completed=%p *completed=%p\n",
        (void *)task,
        (void *)ex,
        ns,
        (void *)completed,
        completed ? (void *)*completed : nullptr);
#endif
    monad_async_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_suspend_for_duration_cancel, completed);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "suspend_for_duration *completed=%p\n",
        (void *)task,
        (void *)ex,
        completed ? (void *)*completed : nullptr);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        if (ret.error.value == ETIME && ns > 0) {
            // io_uring returns timeouts as failure with ETIME, so
            // filter those out
            return monad_async_make_success(0);
        }
        return ret;
    }
    return monad_async_make_success(0);
}

static inline monad_async_result
monad_async_task_claim_registered_io_buffer_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    task->head.ticks_when_suspended_completed =
        get_ticks_count(memory_order_relaxed);
    if (task->please_cancel_invoked) {
        task->head.result = monad_async_make_failure(ECANCELED);
    }
    else {
        task->head.result = monad_async_make_success(0);
    }
    assert(
        atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire) == true);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, false, memory_order_release);
    LIST_REMOVE(
        ex->tasks_suspended_awaiting[task->head.priority.cpu],
        task,
        (size_t *)nullptr);

    assert(
        ex->registered_buffers[task->io_buffer_awaiting_is_for_write]
            .tasks_awaiting.front == &task->io_buffer_awaiting);
    LIST_REMOVE(
        ex->registered_buffers[task->io_buffer_awaiting_is_for_write]
            .tasks_awaiting,
        &task->io_buffer_awaiting,
        (size_t *)nullptr);
    // Force this to true to mark that this task was resumed due to i/o buffer
    // await
    task->io_buffer_awaiting_is_for_write = true;

    atomic_store_explicit(
        &task->head.is_suspended_completed, true, memory_order_release);
    // We need to ensure that the order of tasks being resumed matches the order
    // of suspension pending an i/o buffer, so insert at the right location
    struct monad_async_task_impl *pos =
        ex->tasks_suspended_completed[task->head.priority.cpu].front;
    for (; pos != nullptr && pos->io_buffer_awaiting_is_for_write == true;
         pos = pos->next) {
    }
    if (pos == nullptr) {
        LIST_APPEND(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            (size_t *)nullptr);
    }
    else if (
        pos == ex->tasks_suspended_completed[task->head.priority.cpu].front) {
        LIST_PREPEND(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            (size_t *)nullptr);
    }
    else {
        LIST_INSERT(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            pos,
            task,
            (size_t *)nullptr);
    }
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_claim_registered_io_buffer(
    monad_async_task_registered_io_buffer *buffer, monad_async_task task_,
    size_t bytes_requested,
    struct monad_async_task_claim_registered_io_buffer_flags flags)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_invoked) {
        return monad_async_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    if (bytes_requested >
        ex->registered_buffers[flags.for_write_ring].buffer_size[1]) {
        assert(false);
        return monad_async_make_failure(EINVAL);
    }
    bool const is_large_page =
        (bytes_requested >
         ex->registered_buffers[flags.for_write_ring].buffer_size[0]);
    if (ex->registered_buffers[flags.for_write_ring].free[is_large_page] ==
            nullptr ||
        ex->registered_buffers[flags.for_write_ring].tasks_awaiting.count > 0) {
        if (flags.fail_dont_suspend ||
            ex->registered_buffers[flags.for_write_ring].size == 0 ||
            ex->registered_buffers[flags.for_write_ring].buffers[0].iov_len !=
                ex->registered_buffers[flags.for_write_ring]
                    .buffer_size[is_large_page]) {
            return monad_async_make_failure(ENOMEM);
        }
        LIST_APPEND(
            ex->registered_buffers[flags.for_write_ring].tasks_awaiting,
            &task->io_buffer_awaiting,
            (size_t *)nullptr);
        task->io_buffer_awaiting_is_for_write = flags.for_write_ring;
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p suspends task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d\n",
            (void *)ex,
            (void *)task,
            flags.for_write_ring,
            is_large_page);
        fflush(stdout);
#endif
        MONAD_ASYNC_TRY_RESULT(
            ,
            monad_async_executor_suspend_impl(
                ex,
                task,
                monad_async_task_claim_registered_io_buffer_cancel,
                nullptr));
        // This task no longer is resumed due to i/o buffer wait
        task->io_buffer_awaiting_is_for_write = false;
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d\n",
            (void *)ex,
            (void *)task,
            flags.for_write_ring,
            is_large_page);
        fflush(stdout);
#endif
        if (task->please_cancel_invoked) {
            return monad_async_make_failure(ECANCELED);
        }
        assert(
            ex->registered_buffers[flags.for_write_ring].free[is_large_page] !=
            nullptr);
    }
    struct monad_async_executor_free_registered_buffer *p =
        ex->registered_buffers[flags.for_write_ring].free[is_large_page];
    ex->registered_buffers[flags.for_write_ring].free[is_large_page] = p->next;
    buffer->index = flags.for_write_ring ? -(int)p->index : (int)p->index;
    buffer->iov[0].iov_base = (void *)p;
    buffer->iov[0].iov_len =
        ex->registered_buffers[flags.for_write_ring].buffer_size[is_large_page];
    size_t const pagesize = (is_large_page ? 2 * 1024 * 1024 : 4096);
    if (buffer->iov[0].iov_len > pagesize &&
        monad_async_memory_accounting() ==
            monad_async_memory_accounting_kind_commit_charge) {
        // Explicit commit
        void *mem = mmap(
            (char *)buffer->iov[0].iov_base + pagesize,
            buffer->iov[0].iov_len - pagesize,
            PROT_READ | PROT_WRITE,
            is_large_page ? (MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB |
                             (21 << MAP_HUGE_SHIFT) /* 2Mb pages */)
                          : (MAP_PRIVATE | MAP_ANONYMOUS),
            -1,
            0);
        if (mem == MAP_FAILED) {
            return monad_async_make_failure(errno);
        }
    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p hands out registered i/o buffer %p is_for_write=%d "
        "is_large_page=%d explicit commit=%d\n",
        (void *)ex,
        (void *)p,
        flags.for_write_ring,
        is_large_page,
        buffer->iov[0].iov_len > pagesize &&
            monad_async_memory_accounting() ==
                monad_async_memory_accounting_kind_commit_charge);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_release_registered_io_buffer(
    monad_async_task task_, int buffer_index)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    bool const is_for_write = (buffer_index < 0);
    if (is_for_write) {
        buffer_index = -buffer_index;
    }
    if (buffer_index <= 0 ||
        (unsigned)buffer_index > ex->registered_buffers[is_for_write].size) {
        assert(false);
        return monad_async_make_failure(EINVAL);
    }
    struct iovec *iov =
        &ex->registered_buffers[is_for_write].buffers[buffer_index - 1];
    bool const is_large_page =
        (iov->iov_len > ex->registered_buffers[is_for_write].buffer_size[0]);
    struct monad_async_executor_free_registered_buffer *p =
        (struct monad_async_executor_free_registered_buffer *)iov->iov_base;
    p->index = (unsigned)buffer_index;
    p->next = ex->registered_buffers[is_for_write].free[is_large_page];
    ex->registered_buffers[is_for_write].free[is_large_page] = p;
    size_t const pagesize = (is_large_page ? 2 * 1024 * 1024 : 4096);
    if (iov[0].iov_len > pagesize) {
        if (monad_async_memory_accounting() ==
            monad_async_memory_accounting_kind_commit_charge) {
            // Explicit decommit
            void *mem = mmap(
                (char *)iov[0].iov_base + pagesize,
                iov[0].iov_len - pagesize,
                PROT_NONE,
                is_large_page
                    ? (MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE |
                       MAP_HUGETLB | (21 << MAP_HUGE_SHIFT) /* 2Mb pages */)
                    : (MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE),
                -1,
                0);
            if (mem == MAP_FAILED) {
                return monad_async_make_failure(errno);
            }
        }
        else {
            // Lazy free on memory pressure, OOM killer will not count pages so
            // marked
            madvise(
                (char *)iov[0].iov_base + pagesize,
                iov[0].iov_len - pagesize,
                MADV_FREE);
        }
    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p gets back registered i/o buffer %p is_for_write=%d "
        "is_large_page=%d explicit decommit=%d lazy free=%d will resume "
        "awaiting task=%d\n",
        (void *)ex,
        (void *)p,
        is_for_write,
        is_large_page,
        iov[0].iov_len > pagesize &&
            monad_async_memory_accounting() ==
                monad_async_memory_accounting_kind_commit_charge,
        iov[0].iov_len > pagesize &&
            monad_async_memory_accounting() ==
                monad_async_memory_accounting_kind_over_commit,
        ex->registered_buffers[is_for_write].tasks_awaiting.count > 0);
    fflush(stdout);
#endif
    if (ex->registered_buffers[is_for_write].tasks_awaiting.count > 0) {
        struct monad_async_task_impl *task =
            (struct monad_async_task_impl
                 *)((char *)ex->registered_buffers[is_for_write]
                        .tasks_awaiting.front -
                    offsetof(struct monad_async_task_impl, io_buffer_awaiting));
        (void)monad_async_task_claim_registered_io_buffer_cancel(ex, task);
    }
    return monad_async_make_success(0);
}
