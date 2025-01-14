#include "executor.h"

#include "task.h"

#include <monad/boost_result.h>
#include <monad/config.h>
#include <monad/context/config.h>
#include <monad/context/context_switcher.h>
#include <monad/util/ticks_count.h>

#include "executor_impl.h"
#include "task_impl.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include <liburing.h>
#include <limits.h>
#include <poll.h>
#include <sys/mman.h>

#if MONAD_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif

static inline monad_c_result
monad_async_task_claim_registered_io_write_buffer_resume_with_error_no_buffers_remaining(
    struct monad_async_executor_impl *ex, bool const is_for_write,
    bool const is_large_page);

static inline monad_cpu_ticks_count_t ticks_per_sec()
{
    static monad_cpu_ticks_count_t v;
    if (v == 0) {
        v = monad_ticks_per_second();
    }
    return v;
}

monad_c_result monad_async_executor_create(
    monad_async_executor *ex, struct monad_async_executor_attr *attr)
{
    struct monad_async_executor_impl *p =
        (struct monad_async_executor_impl *)calloc(
            1, sizeof(struct monad_async_executor_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
        (void)monad_async_executor_destroy((monad_async_executor)p),
        monad_async_executor_create_impl(p, attr));
    *ex = (monad_async_executor)p;
    return monad_c_make_success(0);
}

monad_c_result monad_async_executor_destroy(monad_async_executor ex_)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    if (ex->head.total_io_submitted != ex->head.total_io_completed) {
        fprintf(
            stderr,
            "FATAL: On executor destroy, total_io_submitted = %lu "
            "total_io_completed = %lu. If these don't match, it generally "
            "means io_uring ops were leaked e.g. multiple suspend for "
            "durations were issued by a task without cancelling the preceding "
            "ones. You should fix this, as it will eventually overflow "
            "io_uring.\n",
            ex->head.total_io_submitted,
            ex->head.total_io_completed);
        abort();
    }
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_async_executor_destroy_impl(ex));
    free(ex);
    return monad_c_make_success(0);
}

struct launch_pending_tasks_state
{
    struct monad_async_executor_impl *ex;
    ssize_t const *max_items;

    ssize_t items;
    LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
    ssize_t tasks_pending_launch_count;
    monad_async_priority current_priority;
};

static inline monad_c_result monad_async_executor_impl_launch_pending_tasks(
    void *user_ptr, monad_context fake_current_context)
{
    struct launch_pending_tasks_state *state =
        (struct launch_pending_tasks_state *)user_ptr;
    while (state->current_priority < monad_async_priority_max) {
        if (state->tasks_pending_launch[state->current_priority].count == 0) {
            state->current_priority++;
            continue;
        }
        // Not greater equal as haven't done the op yet
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
            state->ex
                ->tasks_running[monad_async_task_effective_cpu_priority(task)],
            task,
            &state->ex->head.tasks_running);
        atomic_store_explicit(
            &task->head.is_running, true, memory_order_release);
        atomic_store_explicit(
            &task->head.is_pending_launch, false, memory_order_release);
        task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
        atomic_store_explicit(
            &state->ex->head.current_task, &task->head, memory_order_release);
        // This may suspend, in which case we shall either resume above
        // or it wil return (depends on context switch implementation)
        atomic_load_explicit(
            &task->head.derived.context->switcher, memory_order_acquire)
            ->resume(fake_current_context, task->head.derived.context);
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has launched %zu pending tasks\n",
        (void *)state->ex,
        state->items);
    fflush(stdout);
#endif
    return monad_c_make_success(0);
}

struct resume_tasks_state
{
    struct monad_async_executor_impl *ex;
    ssize_t const *global_max_items, local_max_items;
    struct list_define_p_monad_async_task_impl_t *wait_list;

    ssize_t items;
    monad_async_priority current_priority;
};

static inline monad_c_result monad_async_executor_impl_resume_tasks(
    void *user_ptr, monad_context fake_current_context)
{
    struct resume_tasks_state *state = (struct resume_tasks_state *)user_ptr;
    while (state->current_priority < monad_async_priority_max) {
        struct list_define_p_monad_async_task_impl_t *wait_list =
            &state->wait_list[state->current_priority];
        if (wait_list->count == 0) {
            state->current_priority++;
            continue;
        }
        if (state->items >= *state->global_max_items ||
            state->items >= state->local_max_items) {
            goto exit;
        }
        ++state->items;
        // Resume execution of the task. If it suspends on
        // another operation, or exits, the loop will resume
        // iterating above or return here
        struct monad_async_task_impl *task = wait_list->front;
        atomic_load_explicit(
            &task->head.derived.context->switcher, memory_order_acquire)
            ->resume(fake_current_context, task->head.derived.context);
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
    return monad_c_make_success(0);
}

struct resume_max_concurrent_io_tasks_state
{
    struct monad_async_executor_impl *ex;
    ssize_t const *global_max_items;

    ssize_t items;
};

static inline monad_c_result
monad_async_executor_impl_resume_max_concurrent_io_tasks(
    void *user_ptr, monad_context fake_current_context)
{
    struct resume_max_concurrent_io_tasks_state *state =
        (struct resume_max_concurrent_io_tasks_state *)user_ptr;
    while (state->ex->max_io_concurrency.count > 0 &&
           state->items < *state->global_max_items) {
        uint64_t const current_io_concurrency =
            state->ex->head.total_io_submitted -
            state->ex->head.total_io_completed;
        if (current_io_concurrency >= state->ex->max_io_concurrency.limit) {
            break;
        }
        ++state->items;
        // Resume execution of the task. If it suspends on
        // another operation, or exits, the loop will resume
        // iterating above or return here
        struct monad_async_task_impl *task =
            (struct monad_async_task_impl *)((char *)state->ex
                                                 ->max_io_concurrency.front -
                                             offsetof(
                                                 struct monad_async_task_impl,
                                                 max_concurrent_io_awaiting));
        // Unlike anywhere else, tasks suspended due to max_concurrent_io aren't
        // suspended for any other reason so migrate them to the suspended
        // completed list
        task->head.derived.result = monad_c_make_success(0);
        assert(
            atomic_load_explicit(
                &task->head.is_suspended_awaiting, memory_order_acquire) ==
            true);
        atomic_store_explicit(
            &task->head.is_suspended_awaiting, false, memory_order_release);
        LIST_REMOVE(
            state->ex->tasks_suspended_awaiting
                [monad_async_task_effective_cpu_priority(task)],
            task,
            (size_t *)nullptr);
        atomic_store_explicit(
            &task->head.is_suspended_completed, true, memory_order_release);
        LIST_APPEND(
            state->ex->tasks_suspended_completed
                [monad_async_task_effective_cpu_priority(task)],
            task,
            (size_t *)nullptr);
        atomic_load_explicit(
            &task->head.derived.context->switcher, memory_order_acquire)
            ->resume(fake_current_context, task->head.derived.context);
    }
    return monad_c_make_success(0);
}

static inline monad_c_result monad_async_executor_run_impl(
    struct monad_async_executor_impl *ex, ssize_t max_items,
    const struct timespec *timeout_)
{
    struct timespec const *timeout = timeout_;
    struct launch_pending_tasks_state launch_pending_tasks_state = {
        .ex = ex, .max_items = &max_items};
    bool timed_out = false;
    bool retry_after_this = false;
    const struct timespec no_waiting = {.tv_sec = 0, .tv_nsec = 0};
    const struct timespec single_millisecond_waiting = {
        .tv_sec = 0, .tv_nsec = 1000000};
    const struct timespec stuck_buffers_check_waiting = {
        .tv_sec = 0, .tv_nsec = 500000000};
    do {
        timed_out = false;
        retry_after_this = false;
        monad_cpu_ticks_count_t const launch_begin =
            get_ticks_count(memory_order_relaxed);
        if (atomic_load_explicit(
                &ex->need_to_empty_eventfd, memory_order_acquire) ||
            atomic_load_explicit(
                &ex->head.tasks_pending_launch, memory_order_acquire) > 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p begins processing tasks pending launch\n",
                (void *)ex);
            fflush(stdout);
#endif
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
                        launch_pending_tasks_state.tasks_pending_launch
                            [monad_async_task_effective_cpu_priority(task)],
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
                    return monad_c_make_failure(errno);
                }
                atomic_store_explicit(
                    &ex->need_to_empty_eventfd, false, memory_order_release);
                timeout = &no_waiting;
                timeout_ = nullptr;
            }
            atomic_unlock(&ex->lock);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p has extracted %zd processing tasks pending "
                "launch\n",
                (void *)ex,
                launch_pending_tasks_state.tasks_pending_launch_count);
            fflush(stdout);
#endif
        }
        if (atomic_load_explicit(
                &ex->head.tasks_suspended, memory_order_acquire) > 0) {
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                if (ex->tasks_suspended_completed[n].count > 0) {
                    timeout = &no_waiting;
                    timeout_ = nullptr;
                    break;
                }
            }
        }
        if (launch_pending_tasks_state.tasks_pending_launch_count > 0) {
            assert(
                launch_pending_tasks_state.tasks_pending_launch_count <=
                max_items);
            timeout = &no_waiting;
            timeout_ = nullptr;
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                while (
                    max_items > 0 &&
                    launch_pending_tasks_state.tasks_pending_launch[n].count >
                        0) {
                    struct monad_async_task_impl *task =
                        launch_pending_tasks_state.tasks_pending_launch[n]
                            .front;
                    monad_context_switcher task_switcher = atomic_load_explicit(
                        &task->head.derived.context->switcher,
                        memory_order_acquire);
                    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                        task_switcher->resume_many(
                            task_switcher,
                            monad_async_executor_impl_launch_pending_tasks,
                            &launch_pending_tasks_state));
                    // launch_pending_tasks_state cannot gain new higher
                    // priority items through resumption
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
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p ends processing tasks pending launch\n",
                (void *)ex);
            fflush(stdout);
#endif
        }
        monad_cpu_ticks_count_t const launch_end =
            get_ticks_count(memory_order_relaxed);
        ex->head.total_ticks_in_task_launch += launch_end - launch_begin;

        if (ex->ring.ring_fd != 0) {
            monad_cpu_ticks_count_t const io_uring_begin =
                get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf("*** Executor %p begins processing io_uring\n", (void *)ex);
            fflush(stdout);
#endif
#ifndef NDEBUG
            if (*ex->ring.sq.kflags & IORING_SQ_CQ_OVERFLOW) {
                fprintf(
                    stderr,
                    "WARNING: io_uring indicates IORING_SQ_CQ_OVERFLOW on the "
                    "non-write ring! cqes awaiting = %u. You should enlarge "
                    "the io_uring entries from %u!\n",
                    io_uring_cq_ready(&ex->ring),
                    ex->ring.sq.ring_entries);
            }
#endif
            struct io_uring_cqe *cqe = nullptr;
            struct io_uring *ring = nullptr;
            // If SQPOLL, this does nothing so is safe to always call
            int r = io_uring_submit(&ex->ring);
            if (r < 0 && r != -EINTR) {
                return monad_c_make_failure(-r);
            }
            r = 0;
            // We may now have free SQE slots after the submit
            bool need_to_submit_again = false;
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
                        struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
                        if (sqe == nullptr) {
                            break;
                        }
                        need_to_submit_again = true;
                        ex->head.total_io_submitted++;
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
                        monad_context_switcher task_switcher =
                            atomic_load_explicit(
                                &task->head.derived.context->switcher,
                                memory_order_acquire);
                        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                            task_switcher->resume_many(
                                task_switcher,
                                monad_async_executor_impl_resume_tasks,
                                &resume_tasks_state));
                        if (resume_tasks_state.items > 0) {
                            max_items--;
                            // Resuming tasks may have introduced higher
                            // priority tasks to resume instead
                            resume_tasks_state.current_priority =
                                monad_async_priority_high;
                        }
                        break;
                    }
                }
                if (done) {
                    break;
                }
            }
            if (need_to_submit_again) {
                // Immediately submit any newly enqueued i/o
                r = io_uring_submit(&ex->ring);
                if (r < 0 && r != -EINTR) {
                    return monad_c_make_failure(-r);
                }
            }
            r = 1;
            // If there are extant file write ops only
            if (ex->wr_ring_ops_outstanding > 0) {
#ifndef NDEBUG
                if (*ex->wr_ring.sq.kflags & IORING_SQ_CQ_OVERFLOW) {
                    fprintf(
                        stderr,
                        "WARNING: io_uring indicates IORING_SQ_CQ_OVERFLOW on "
                        "the write ring! cqes awaiting = %u. You should "
                        "enlarge the io_uring entries from %u!\n",
                        io_uring_cq_ready(&ex->wr_ring),
                        ex->wr_ring.sq.ring_entries);
                }
#endif
                ring = &ex->wr_ring;
                /* This will use syscall enter if either the submission or
                completion queues have flagged that they need it e.g. the SQPOLL
                thread has gone to sleep and needs reawakening, or the CQE queue
                has entered overflow. This means it can take some time,
                occasionally, but it's better than an explicit call to
                io_uring_wait_cqes().
                */
                r = io_uring_submit(ring);
                if (r < 0 && r != -EINTR) {
                    return monad_c_make_failure(-r);
                }
                r = 0;
                need_to_submit_again = false;
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
                            need_to_submit_again = true;
                            ex->head.total_io_submitted++;
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
                            monad_context_switcher task_switcher =
                                atomic_load_explicit(
                                    &task->head.derived.context->switcher,
                                    memory_order_acquire);
                            BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                                task_switcher->resume_many(
                                    task_switcher,
                                    monad_async_executor_impl_resume_tasks,
                                    &resume_tasks_state));
                            if (resume_tasks_state.items > 0) {
                                max_items--;
                                // Resuming tasks may have introduced higher
                                // priority tasks to resume instead
                                resume_tasks_state.current_priority =
                                    monad_async_priority_high;
                            }
                            break;
                        }
                    }
                    if (done) {
                        break;
                    }
                }
                if (need_to_submit_again) {
                    r = io_uring_submit(ring);
                    if (r < 0 && r != -EINTR) {
                        return monad_c_make_failure(-r);
                    }
                }
                r = io_uring_peek_cqe(ring, &cqe);
                if (timeout == nullptr || timeout != &no_waiting ||
                    timespec_to_ns(timeout) > 1000000) {
                    // The write ring must be frequently polled while there are
                    // extant write ops
                    timeout = &single_millisecond_waiting;
                    timeout_ = nullptr;
                }
            }
            // If write ring did not have a CQE for us, examine the non-write
            // ring
            if (cqe == nullptr) {
                ring = &ex->ring;
                // Speculatively peek to avoid syscalls
                r = io_uring_peek_cqe(ring, &cqe);
                if (cqe == nullptr) {
                    if (atomic_load_explicit(
                            &ex->head.tasks_suspended_sqe_exhaustion,
                            memory_order_acquire) > 0) {
                        // If there are tasks awaiting SQE slots, no waiting so
                        // we can clear the backlog ASAP
                        timeout = &no_waiting;
                        timeout_ = nullptr;
                    }
                    else if (
                        (ex->registered_buffers[0].buffer[0].free == nullptr ||
                         ex->registered_buffers[0].buffer[1].free == nullptr) &&
                        ex->registered_buffers[0]
                                    .buffer[0]
                                    .tasks_awaiting.count +
                                ex->registered_buffers[0]
                                    .buffer[1]
                                    .tasks_awaiting.count >
                            0 &&
                        (timeout == nullptr ||
                         timespec_to_ns(timeout) >
                             timespec_to_ns(&stuck_buffers_check_waiting))) {
                        timeout = &stuck_buffers_check_waiting;
                        timeout_ = nullptr;
                    }
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
                    if (timeout == nullptr) {
                        printf(
                            "*** Executor %p submits and waits forever due "
                            "to "
                            "infinite timeout. sqes=%u cqes=%u\n",
                            (void *)ex,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));
                    }
                    else {
                        printf(
                            "*** Executor %p waits for a "
                            "non-infinite "
                            "timeout %ld-%ld. sqes=%u cqes=%u\n",
                            (void *)ex,
                            timeout->tv_sec,
                            timeout->tv_nsec,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));
                    }
                    fflush(stdout);
#endif
                    if (timeout != nullptr && timeout->tv_sec == 0 &&
                        timeout->tv_nsec == 0 &&
                        (ring->flags & IORING_SETUP_SQPOLL) != 0 &&
                        (*ring->sq.kflags & IORING_SQ_NEED_WAKEUP) == 0) {
                        // If SQPOLL and zero timeout and no reason to call
                        // syscall io_uring_enter, skip that.
                    }
                    else {
                        monad_cpu_ticks_count_t const sleep_begin =
                            get_ticks_count(memory_order_relaxed);
                        // This is the new faster io_uring wait syscall
                        // It calls syscall io_uring_enter2. It does not have an
                        // optimisation for zero timeout.
                        r = io_uring_wait_cqes(
                            ring,
                            &cqe,
                            1,
                            (struct __kernel_timespec *)timeout,
                            nullptr);
                        if (r == 0 && cqe != nullptr) {
                            r = 1;
                        }
                        // Ignore temporary failure
                        if (r == -EINTR) {
                            r = 0;
                        }
                        monad_cpu_ticks_count_t const sleep_end =
                            get_ticks_count(memory_order_relaxed);
                        ex->head.total_ticks_sleeping +=
                            sleep_end - sleep_begin;

                        // Check for tasks deadlocked by lack of i/o buffers and
                        // give one a kick if necessary
                        for (int is_large_page = 0; is_large_page < 2;
                             is_large_page++) {
                            if (ex->registered_buffers[0]
                                        .buffer[is_large_page]
                                        .free == nullptr &&
                                ex->registered_buffers[0]
                                        .buffer[is_large_page]
                                        .tasks_awaiting.front != nullptr) {
                                monad_cpu_ticks_count_t const
                                    ticks_since_last_buffer_free =
                                        sleep_end - ex->registered_buffers[0]
                                                        .buffer[is_large_page]
                                                        .ticks_last_free;
                                if (ticks_since_last_buffer_free >=
                                    ticks_per_sec() / 2) {
                                    MONAD_CONTEXT_CHECK_RESULT(
                                        monad_async_task_claim_registered_io_write_buffer_resume_with_error_no_buffers_remaining(
                                            ex, false, is_large_page));
                                }
                            }
                        }
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
                    return monad_c_make_failure(-r);
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** %ld. Executor %p sees cqe=%p from io_uring wait. "
                "wr_ring=%d. "
                "sqes=%u "
                "cqes=%u max_items=%ld\n",
                time(nullptr),
                (void *)ex,
                (void *)cqe,
                ring == &ex->wr_ring,
                io_uring_sq_ready(ring),
                io_uring_cq_ready(ring),
                max_items);
            fflush(stdout);
#endif
            // Always empty the completions queue irrespective of max_items
            uint32_t total_io_completed_to_subtract = 0;
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
                fflush(stdout);
#endif
                if (cqe->user_data == 0 && cqe->res <= 0 && cqe->flags == 0) {
                    // Empty CQE. Theroretically no longer possible since recent
                    // other changes.
                    fprintf(
                        stderr,
                        "FATAL: Empty CQE received. This should supposedly "
                        "never happen.\n");
                    abort();
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
                    assert(0 == memcmp(task->magic, "MNASTASK", 8));
                    assert(
                        !(task->please_cancel_status ==
                              please_cancel_invoked_seen &&
                          task->please_cancel_invoked_suspending_ops_remaining >
                              0));
                    if (task->please_cancel_status !=
                            please_cancel_not_invoked &&
                        task->please_cancel_status !=
                            please_cancel_invoked_seen) {
                        /* It would seem from testing that there is always a
                        one-one relationship between SQE and CQE, so we always
                        get one CQE for every SQE submitted.

                        If we cancel an io_uring operation already submitted,
                        the following can occur:

                        1. We get back a CQE saying -EALREADY which means
                        io_uring refuses to cancel that operation.

                        2. -ENOENT which means io_uring has decided it has
                        already completed that operation.

                        3. The original operation may return -ECANCELED, but it
                        may also sometimes not do so.

                        4. The CQE for the original operation and the
                        cancellation of that operation can appear in any order,
                        and may have other CQEs in between them.

                        To this end, we have a small state machine here which
                        doesn't differentiate between CQE types, but rather
                        counts their receipt. We don't resume the task until the
                        SECOND CQE arrives. This avoids issues with say i/o
                        buffers getting written into after the task has been
                        unwound.

                        We also zap any success or error values from io_uring
                        into a single ECANCELED for the resumed task to trigger
                        cancellation.
                        */
                        switch (task->please_cancel_status) {
                        case please_cancel_invoked_not_seen_yet:
                            task->please_cancel_status =
                                please_cancel_invoked_seen_awaiting_uring;
                            task->please_cancel_invoked_suspending_ops_remaining =
                                1;
                            break;
                        case please_cancel_invoked_seen_awaiting_uring:
                            task->please_cancel_invoked_suspending_ops_remaining--;
                            break;
                        default:
                            abort();
                        }
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p cancelling task %p "
                            "please_cancel_status = %d "
                            "please_cancel_invoked_suspending_ops_"
                            "remaining = %d\n",
                            i,
                            (void *)ex,
                            (void *)task,
                            task->please_cancel_status,
                            task->please_cancel_invoked_suspending_ops_remaining);
                        fflush(stdout);
#endif
                    }
                    if (atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire) &&
                        task->please_cancel_invoked_suspending_ops_remaining <=
                            0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p resumes suspended task "
                            "%p (cpu priority=%d, i/o priority=%d)\n",
                            i,
                            (void *)ex,
                            (void *)task,
                            (int)monad_async_task_effective_cpu_priority(task),
                            (int)task->head.priority.io);
                        fflush(stdout);
#endif
                        task->head.ticks_when_suspended_completed =
                            get_ticks_count(memory_order_relaxed);
                        if (task->please_cancel_status !=
                                please_cancel_not_invoked &&
                            task->please_cancel_status !=
                                please_cancel_invoked_seen) {
                            if (cqe->res < 0) {
                                switch (cqe->res) {
                                case -ECANCELED:
                                case -ETIME:
                                case -EALREADY:
                                case -ENOENT:
                                    break;
                                case -EINVAL:
                                    fprintf(
                                        stderr,
                                        "FATAL: Executor told cancellation "
                                        "request had invalid arguments, this "
                                        "will be a logic error.\n");
                                    abort();
                                default:
                                    fprintf(
                                        stderr,
                                        "FATAL: Executor told cancellation "
                                        "request has failed with '%s', this "
                                        "will be a logic error.\n",
                                        strerror(-cqe->res));
                                    abort();
                                }
                            }
                            task->head.derived.result =
                                monad_c_make_failure(ECANCELED);
                            task->please_cancel_status =
                                please_cancel_invoked_seen;
                        }
                        else if (cqe->res < 0) {
                            task->head.derived.result =
                                monad_c_make_failure(-cqe->res);
                        }
                        else {
                            task->head.derived.result =
                                monad_c_make_success(cqe->res);
                        }
                        atomic_store_explicit(
                            &task->head.is_suspended_awaiting,
                            false,
                            memory_order_release);
                        LIST_REMOVE(
                            ex->tasks_suspended_awaiting
                                [monad_async_task_effective_cpu_priority(task)],
                            task,
                            (size_t *)nullptr);
                        atomic_store_explicit(
                            &task->head.is_suspended_completed,
                            true,
                            memory_order_release);
                        LIST_APPEND(
                            ex->tasks_suspended_completed
                                [monad_async_task_effective_cpu_priority(task)],
                            task,
                            (size_t *)nullptr);
                    }
                    else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p NOT resuming suspended task "
                            "%p (cpu priority=%d, i/o priority=%d) as "
                            "is_suspended_awaiting = %d "
                            "please_cancel_invoked_suspending_ops_remaining = "
                            "%d\n",
                            i,
                            (void *)ex,
                            (void *)task,
                            (int)monad_async_task_effective_cpu_priority(task),
                            (int)task->head.priority.io,
                            atomic_load_explicit(
                                &task->head.is_suspended_awaiting,
                                memory_order_acquire),
                            task->please_cancel_invoked_suspending_ops_remaining);
                        fflush(stdout);
#endif
                    }
                }
                else if (iostatus != nullptr) {
                    // result contains the pointer to the task which is to
                    // receive the i/o completion. It gets overwritten by the
                    // actual result of the i/o below, and that result will
                    // never be a valid pointer, so this check should be
                    // reliable.
                    task = (struct monad_async_task_impl *)iostatus->task_;
                    struct monad_async_task_registered_io_buffer *tofill =
                        iostatus->tofill_;
                    assert(task != nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** %u. Executor %p gets result of i/o %p "
                        "initiated "
                        "by task %p (cpu priority=%d, i/o priority=%d) "
                        "completed = %p is_suspended_for_io = %d "
                        "is_suspended_sqe_exhaustion = %d "
                        "is_suspended_sqe_exhaustion_wr = %d "
                        "is_suspended_io_buffer_exhaustion = %d "
                        "is_suspended_max_concurrency = %d "
                        "is_suspended_awaiting = %d is_suspended_completed = "
                        "%d\n",
                        i,
                        (void *)ex,
                        (void *)iostatus,
                        (void *)task,
                        (int)monad_async_task_effective_cpu_priority(task),
                        (int)task->head.priority.io,
                        (void *)task->completed,
                        atomic_load_explicit(
                            &task->head.is_suspended_for_io,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_sqe_exhaustion,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_sqe_exhaustion_wr,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_io_buffer_exhaustion,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_max_concurrency,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire),
                        atomic_load_explicit(
                            &task->head.is_suspended_completed,
                            memory_order_acquire));
                    fflush(stdout);
#endif
                    assert(0 == memcmp(task->magic, "MNASTASK", 8));
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
                        iostatus->result = monad_c_make_failure(-cqe->res);
                    }
                    else {
                        iostatus->result = monad_c_make_success(cqe->res);
                    }
                    if (cqe->flags & IORING_CQE_F_BUFFER) {
                        if (tofill == nullptr) {
                            fprintf(
                                stderr,
                                "FATAL: io_uring chooses buffer but tofill was "
                                "not set!\n");
                            abort();
                        }
                        tofill->index =
                            (int)(cqe->flags >> IORING_CQE_BUFFER_SHIFT);
                        tofill->iov[0] = ex->registered_buffers[0]
                                             .buffers[tofill->index - 1];
                        ex->head.registered_buffers.total_claimed++;
                        ex->head.registered_buffers.ticks_last_claim =
                            get_ticks_count(memory_order_relaxed);
                    }
                    if (cqe->res < 0 && tofill != nullptr) {
                        // There is failure, and either the buffer came from
                        // io_uring or we allocated it and it needs to be freed
                        // as we own it
                        MONAD_CHECK_RESULT(
                            monad_async_task_release_registered_io_buffer(
                                &task->head, tofill->index));
                        memset(tofill, 0, sizeof(*tofill));
                    }
                    if (atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire) &&
                        task->completed != nullptr) {
                        // If completed is set, it means the task is suspended
                        // on an iostatus based i/o and wants to be resumed. If
                        // completed is null, it means the task is suspended on
                        // a non-iostatus based i/o and it does not want to be
                        // resumed by iostatus i/o.
                        assert(atomic_load_explicit(
                            &task->head.is_suspended_for_io,
                            memory_order_acquire));
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p handles result of i/o %p "
                            "initiated by task %p by executing resume task "
                            "(which may demur). "
                            "completed = %p is_suspended_sqe_exhaustion = %d "
                            "is_suspended_sqe_exhaustion_wr = %d "
                            "is_suspended_io_buffer_exhaustion = %d "
                            "is_suspended_max_concurrency = %d "
                            "is_suspended_awaiting = %d\n",
                            i,
                            (void *)ex,
                            (void *)iostatus,
                            (void *)task,
                            (void *)task->completed,
                            atomic_load_explicit(
                                &task->head.is_suspended_sqe_exhaustion,
                                memory_order_acquire),
                            atomic_load_explicit(
                                &task->head.is_suspended_sqe_exhaustion_wr,
                                memory_order_acquire),
                            atomic_load_explicit(
                                &task->head.is_suspended_io_buffer_exhaustion,
                                memory_order_acquire),
                            atomic_load_explicit(
                                &task->head.is_suspended_max_concurrency,
                                memory_order_acquire),
                            atomic_load_explicit(
                                &task->head.is_suspended_awaiting,
                                memory_order_acquire));
                        fflush(stdout);
#endif
                        *task->completed = iostatus;
                        task->completed = nullptr;
                        cqe->res = (int)task->head.io_completed_not_reaped;
                        goto resume_task;
                    }
                }
                else if (magic == EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC) {
                    if ((cqe->flags & IORING_CQE_F_MORE) != IORING_CQE_F_MORE) {
                        // io_uring has dropped the eventfd poll
                        monad_c_result r2 =
                            monad_async_executor_setup_eventfd_polling(ex);
                        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r2)) {
                            // io_uring submit failed, if this happens something
                            // is very wrong
                            abort();
                        }
                    }
                    total_io_completed_to_subtract++;
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
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
            printf(
                "*** Executor %p has dequeued %u completions from "
                "io_uring\n",
                (void *)ex,
                i);
            fflush(stdout);
#endif
            io_uring_cq_advance(ring, i);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf("*** Executor %p ends processing io_uring\n", (void *)ex);
            fflush(stdout);
#endif
            if (ring == &ex->wr_ring) {
                assert(ex->wr_ring_ops_outstanding >= i);
                if (i > ex->wr_ring_ops_outstanding) {
                    ex->wr_ring_ops_outstanding = 0;
                }
                else {
                    ex->wr_ring_ops_outstanding -= i;
                }
            }
            monad_cpu_ticks_count_t const io_uring_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_io_uring += io_uring_end - io_uring_begin;
            ex->head.total_io_completed += i - total_io_completed_to_subtract;
        }
        else {
            // If io_uring was not enabled for this executor, use the
            // eventfd as the synchronisation object
            if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
                printf(
                    "*** Executor %p waits forever due to infinite "
                    "timeout\n",
                    (void *)ex);
                fflush(stdout);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, nullptr, nullptr);
                monad_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping += sleep_end - sleep_begin;
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_c_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
            else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
                printf(
                    "*** Executor %p does not wait due to zero "
                    "timeout\n",
                    (void *)ex);
                fflush(stdout);
#endif
            }
            else {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
                printf(
                    "*** Executor %p waits for a non-infinite "
                    "timeout "
                    "%ld-%ld\n",
                    (void *)ex,
                    timeout->tv_sec,
                    timeout->tv_nsec);
                fflush(stdout);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, timeout, nullptr);
                monad_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping += sleep_end - sleep_begin;
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_c_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
        }
        if (ex->tasks_exited.count > 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p begins processing tasks exited 1\n",
                (void *)ex);
            fflush(stdout);
#endif
            while (ex->tasks_exited.count > 0) {
                struct monad_async_task_impl *task = ex->tasks_exited.front;
                LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
                atomic_store_explicit(
                    &task->head.current_executor,
                    nullptr,
                    memory_order_release);
                if (task->call_after_suspend_to_executor != nullptr) {
                    monad_c_result (*call_after_suspend_to_executor)(
                        monad_context_task task) =
                        task->call_after_suspend_to_executor;
                    task->call_after_suspend_to_executor = nullptr;
                    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                        call_after_suspend_to_executor(&task->head.derived));
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p ends processing tasks exited 1\n", (void *)ex);
            fflush(stdout);
#endif
        }
        if (atomic_load_explicit(
                &ex->cause_run_to_return, memory_order_acquire) != nullptr) {
            atomic_lock(&ex->lock);
            monad_c_result r = ex->cause_run_to_return_value;
            atomic_store_explicit(
                &ex->cause_run_to_return, nullptr, memory_order_release);
            atomic_unlock(&ex->lock);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p run exits due to cause_run_to_return\n",
                (void *)ex);
            fflush(stdout);
#endif
            return r;
        }
        struct resume_tasks_state resume_tasks_state = {
            .ex = ex,
            .global_max_items = &max_items,
            .local_max_items = (ssize_t)(ex->tasks_suspended_completed
                                             [monad_async_priority_high]
                                                 .count +
                                         ex->tasks_suspended_completed
                                             [monad_async_priority_normal]
                                                 .count +
                                         ex->tasks_suspended_completed
                                             [monad_async_priority_low]
                                                 .count),
            .wait_list = ex->tasks_suspended_completed};
        if (max_items > 0) {
            monad_cpu_ticks_count_t const completions_begin =
                get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf(
                "*** Executor %p begins processing completions\n", (void *)ex);
            fflush(stdout);
#endif
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
                    monad_context_switcher task_switcher = atomic_load_explicit(
                        &task->head.derived.context->switcher,
                        memory_order_acquire);
                    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                        task_switcher->resume_many(
                            task_switcher,
                            monad_async_executor_impl_resume_tasks,
                            &resume_tasks_state));
                    if (resume_tasks_state.items > 0) {
                        // Resuming tasks may have introduced higher priority
                        // tasks to resume instead
                        resume_tasks_state.current_priority =
                            monad_async_priority_high;
                        if (resume_tasks_state.items >= max_items) {
                            max_items = 0;
                        }
                        else {
                            max_items -= resume_tasks_state.items;
                        }
                    }
                    break;
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
            printf("*** Executor %p ends processing completions\n", (void *)ex);
            fflush(stdout);
#endif
            monad_cpu_ticks_count_t const completions_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_task_completion +=
                completions_end - completions_begin;
            if (ex->tasks_exited.count > 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
                printf(
                    "*** Executor %p begins processing tasks exited 2\n",
                    (void *)ex);
                fflush(stdout);
#endif
                while (ex->tasks_exited.count > 0) {
                    struct monad_async_task_impl *task = ex->tasks_exited.front;
                    LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
                    atomic_store_explicit(
                        &task->head.current_executor,
                        nullptr,
                        memory_order_release);
                    if (task->call_after_suspend_to_executor != nullptr) {
                        monad_c_result (*call_after_suspend_to_executor)(
                            monad_context_task task) =
                            task->call_after_suspend_to_executor;
                        task->call_after_suspend_to_executor = nullptr;
                        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                            call_after_suspend_to_executor(
                                &task->head.derived));
                    }
                }
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 3
                printf(
                    "*** Executor %p ends processing tasks exited 2\n",
                    (void *)ex);
                fflush(stdout);
#endif
            }
        }
        struct resume_max_concurrent_io_tasks_state
            resume_max_concurrent_io_tasks_state = {
                .ex = ex, .global_max_items = &max_items};
        if (ex->max_io_concurrency.limit > 0 && max_items > 0 &&
            ex->max_io_concurrency.count > 0) {
            uint64_t const current_io_concurrency =
                ex->head.total_io_submitted - ex->head.total_io_completed;
            if (current_io_concurrency < ex->max_io_concurrency.limit) {
                struct monad_async_task_impl *task =
                    (struct monad_async_task_impl
                         *)((char *)ex->max_io_concurrency.front -
                            offsetof(
                                struct monad_async_task_impl,
                                max_concurrent_io_awaiting));
                monad_context_switcher task_switcher = atomic_load_explicit(
                    &task->head.derived.context->switcher,
                    memory_order_acquire);
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(task_switcher->resume_many(
                    task_switcher,
                    monad_async_executor_impl_resume_max_concurrent_io_tasks,
                    &resume_max_concurrent_io_tasks_state));
                if (resume_max_concurrent_io_tasks_state.items > 0) {
                    if (resume_max_concurrent_io_tasks_state.items >=
                        max_items) {
                        max_items = 0;
                    }
                    else {
                        max_items -= resume_max_concurrent_io_tasks_state.items;
                    }
                }
            }
        }
        ssize_t items_processed = launch_pending_tasks_state.items +
                                  resume_tasks_state.items +
                                  resume_max_concurrent_io_tasks_state.items;
        if (items_processed > 0) {
            return monad_c_make_success((intptr_t)items_processed);
        }
    }
    while (retry_after_this);
    return (timed_out && timeout_ != nullptr) ? monad_c_make_failure(ETIME)
                                              : monad_c_make_success(0);
}

monad_c_result monad_async_executor_run(
    monad_async_executor ex_, size_t max_items, const struct timespec *timeout)
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
    monad_cpu_ticks_count_t const run_begin =
        get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
    printf("*** Executor %p enters run\n", (void *)ex);
    fflush(stdout);
#endif
    monad_c_result ret = monad_async_executor_run_impl(
        ex, (max_items > SSIZE_MAX) ? SSIZE_MAX : (ssize_t)max_items, timeout);
#if MONAD_ASYNC_EXECUTOR_PRINTING >= 2
    printf(
        "*** Executor %p exits run having processed %zu items\n",
        (void *)ex,
        ret.value);
    fflush(stdout);
#endif
    monad_cpu_ticks_count_t const run_end =
        get_ticks_count(memory_order_relaxed);
    ex->head.total_ticks_in_run += run_end - run_begin;
    ex->within_run = false;
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
#if 0
    static monad_context_cpu_ticks_count_t last_run_end;
    if (last_run_end / 10000000000u != run_end / 10000000000u) {
        last_run_end = run_end;
        static monad_context_cpu_ticks_count_t total_ticks_in_run;
        static monad_context_cpu_ticks_count_t total_ticks_in_task_launch;
        static monad_context_cpu_ticks_count_t total_ticks_in_io_uring;
        static monad_context_cpu_ticks_count_t total_ticks_sleeping;
        static monad_context_cpu_ticks_count_t total_ticks_in_task_completion;
        printf(
            "   Executor tasks_suspended_sqe_exhaustion = "
            "%zu io_outstanding = %lu buffers_outstanding = %zu ticks_in_run = "
            "%lu ticks_in_launch = %lu ticks_in_uring = %lu ticks_sleeping = "
            "%lu ticks_in_completion = %lu total_io_completed = %zu "
            "wr_ring_ops_outstanding = %u\n",
            ex->head.tasks_suspended_sqe_exhaustion,
            ex->head.total_io_submitted - ex->head.total_io_completed,
            ex->head.registered_buffers.total_claimed -
                ex->head.registered_buffers.total_released,
            ex->head.total_ticks_in_run - total_ticks_in_run,
            ex->head.total_ticks_in_task_launch - total_ticks_in_task_launch,
            ex->head.total_ticks_in_io_uring - total_ticks_in_io_uring,
            ex->head.total_ticks_sleeping - total_ticks_sleeping,
            ex->head.total_ticks_in_task_completion -
                total_ticks_in_task_completion,
            ex->head.total_io_completed,
            ex->wr_ring_ops_outstanding);
        fflush(stdout);
        total_ticks_in_run = ex->head.total_ticks_in_run;
        total_ticks_in_task_launch = ex->head.total_ticks_in_task_launch;
        total_ticks_in_io_uring = ex->head.total_ticks_in_io_uring;
        total_ticks_sleeping = ex->head.total_ticks_sleeping;
        total_ticks_in_task_completion =
            ex->head.total_ticks_in_task_completion;
    }
#endif
    return ret;
}

monad_c_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_c_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task),
    monad_async_io_status **completed,
    struct monad_async_task_impl *task_to_resume)
{
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
    // One of these must be set to indicate cause of suspension
    assert(
        atomic_load_explicit(
            &task->head.is_suspended_for_io, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion_wr, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_max_concurrency, memory_order_acquire));
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        &task->head);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task->please_cancel = please_cancel;
    task->completed = completed;
#ifndef NDEBUG
    // Trap failure to set result, EFAULT should rarely appear from a syscall
    task->head.derived.result = monad_c_make_failure(EFAULT);
#endif
    atomic_store_explicit(&task->head.is_running, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_running[monad_async_task_effective_cpu_priority(task)],
        task,
        &ex->head.tasks_running);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_suspended_awaiting[monad_async_task_effective_cpu_priority(
            task)],
        task,
        &ex->head.tasks_suspended);
    task->head.ticks_when_suspended_awaiting =
        get_ticks_count(memory_order_relaxed);
    task->head.total_ticks_executed +=
        task->head.ticks_when_suspended_awaiting -
        task->head.ticks_when_resumed;
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p suspends task %p task_to_resume = %p\n",
        (void *)ex,
        (void *)task,
        (void *)task_to_resume);
    fflush(stdout);
#endif
    atomic_load_explicit(
        &task->head.derived.context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(
            task->head.derived.context,
            (task_to_resume == nullptr) ? nullptr
                                        : task_to_resume->head.derived.context);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p resumes task %p (cpu priority=%d, i/o priority=%d)\n",
        (void *)ex,
        (void *)task,
        (int)monad_async_task_effective_cpu_priority(task),
        (int)task->head.priority.io);
    fflush(stdout);
#endif
    task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
    assert(!atomic_load_explicit(
        &task->head.is_suspended_awaiting, memory_order_acquire));
    assert(atomic_load_explicit(
        &task->head.is_suspended_completed, memory_order_acquire));
    atomic_store_explicit(
        &task->head.is_suspended_completed, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_suspended_completed[monad_async_task_effective_cpu_priority(
            task)],
        task,
        &ex->head.tasks_suspended);
    atomic_store_explicit(&task->head.is_running, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_running[monad_async_task_effective_cpu_priority(task)],
        task,
        &ex->head.tasks_running);
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        nullptr);
    atomic_store_explicit(
        &ex->head.current_task, &task->head, memory_order_release);
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
    }
    task->please_cancel = nullptr;
    task->completed = nullptr;
    return task->head.derived.result;
}

monad_c_result monad_async_executor_wake(
    monad_async_executor ex_, monad_c_result const *cause_run_to_return)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    atomic_lock(&ex->lock);
    monad_c_result r =
        monad_async_executor_wake_impl(&ex->lock, ex, cause_run_to_return);
    atomic_unlock(&ex->lock);
    return r;
}

monad_c_result monad_async_executor_submit(
    monad_async_executor ex_, size_t max_items_in_nonwrite_submission_queue,
    size_t max_items_in_write_submission_queue)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    intptr_t ret = 0;
    if (ex->ring.ring_fd != 0 && (0 == max_items_in_nonwrite_submission_queue ||
                                  io_uring_sq_ready(&ex->ring) >=
                                      max_items_in_nonwrite_submission_queue)) {
        int r = io_uring_submit(&ex->ring);
        if (r < 0 && r != -EINTR) {
            return monad_c_make_failure(-r);
        }
        ret++;
    }
    if (ex->wr_ring.ring_fd != 0 && (0 == max_items_in_write_submission_queue ||
                                     io_uring_sq_ready(&ex->wr_ring) >=
                                         max_items_in_write_submission_queue)) {
        int r = io_uring_submit(&ex->wr_ring);
        if (r < 0 && r != -EINTR) {
            return monad_c_make_failure(-r);
        }
        ret++;
    }
    return monad_c_make_success(ret);
}

void monad_async_executor_task_detach(monad_context_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        &task->head);
    if (task->io_submitted.count != 0) {
        fprintf(
            stderr, "FATAL: You cannot detach a task with uncompleted i/o!\n");
        abort();
    }
    // All completed i/o should be reaped before detach
    assert(task->io_completed.count == 0);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task->head.ticks_when_detached = get_ticks_count(memory_order_relaxed);
    task->head.total_ticks_executed +=
        task->head.ticks_when_detached - task->head.ticks_when_resumed;
    atomic_store_explicit(&task->head.is_running, false, memory_order_release);
    atomic_lock(&ex->lock);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_running[monad_async_task_effective_cpu_priority(task)],
        task,
        &ex->head.tasks_running);
    LIST_APPEND(ex->tasks_exited, task, (size_t *)nullptr);
    atomic_unlock(&ex->lock);
    // Reset some settings which users may have changed
    task->head.io_recipient_task = &task->head;
    task->head.priority.cpu = monad_async_priority_normal;
    task->head.priority.io = monad_async_priority_normal;
}

/****************************************************************************/

monad_c_result monad_async_task_attach(
    monad_async_executor ex_, monad_async_task task_,
    monad_context_switcher opt_reparent_switcher)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->head.derived.user_code == nullptr) {
        return monad_c_make_failure(EINVAL);
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
                ex->tasks_running[monad_async_task_effective_cpu_priority(
                    task)],
                task,
                &ex->head.tasks_running);
            atomic_store_explicit(
                &task->head.is_running, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_awaiting, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_awaiting
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_awaiting, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_completed,
                     memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_completed
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_completed,
                false,
                memory_order_release);
        }
        else {
            fprintf(
                stderr,
                "FATAL: Current executor set on a task being attached but I "
                "don't know how to detach it. Are you attaching a task before "
                "executor run has had a chance to clean it up?\n");
            abort();
        }
        atomic_unlock(&ex->lock);
    }
    monad_context_switcher task_switcher = atomic_load_explicit(
        &task->head.derived.context->switcher, memory_order_acquire);
    if (opt_reparent_switcher && opt_reparent_switcher != task_switcher) {
        monad_context_reparent_switcher(
            task->head.derived.context, opt_reparent_switcher);
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
    // Do not set total_ticks_executed, ticks_when_suspended_awaiting,
    // ticks_when_suspended_completed
    atomic_lock(&ex->lock);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_pending_launch, task, &ex->head.tasks_pending_launch);
    if (on_foreign_thread) {
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            (void)atomic_unlock(&ex->lock),
            monad_async_executor_wake_impl(&ex->lock, ex, nullptr));
    }
    atomic_unlock(&ex->lock);
    return monad_c_make_success(0);
}

monad_c_result
monad_async_task_cancel(monad_async_executor ex_, monad_async_task task_)
{
    if (monad_async_task_has_exited(task_)) {
        return monad_c_make_success(0);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (atomic_load_explicit(
            &task->head.is_pending_launch, memory_order_acquire)) {
        atomic_lock(&ex->lock);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Task %p running on executor %p is cancelled immediately as it "
            "was pending launch.\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_pending_launch, task, &ex->head.tasks_pending_launch);
        atomic_store_explicit(
            &task->head.is_pending_launch, false, memory_order_release);
        task->please_cancel_status = please_cancel_cancelled;
        atomic_unlock(&ex->lock);
        atomic_store_explicit(
            &task->head.current_executor, nullptr, memory_order_release);
        return monad_c_make_success(0);
    }
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        fprintf(
            stderr, "TODO: Switch context back to root, and end the task\n");
        abort();
    }
    atomic_lock(&ex->lock);
    if (task->please_cancel_status != please_cancel_not_invoked) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
        char const *awaiting_msg = "i/o";
        if (atomic_load_explicit(
                &task->head.is_suspended_sqe_exhaustion,
                memory_order_acquire)) {
            awaiting_msg = "a non-write io_uring SQE";
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_sqe_exhaustion_wr,
                     memory_order_acquire)) {
            awaiting_msg = "a write io_uring SQE";
        }
        printf(
            "*** Task %p running on executor %p currently suspended "
            "awaiting %s has already been requested to cancel. "
            "please_cancel_status = %d\n",
            (void *)task,
            (void *)ex,
            awaiting_msg,
            task->please_cancel_status);
        fflush(stdout);
#endif
        atomic_unlock(&ex->lock);
        return monad_c_make_failure(EAGAIN);
    }
    if (atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion_wr, memory_order_acquire)) {
        // Invoke the cancellation routine
        if (task->please_cancel == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
            char const *awaiting_msg = "i/o";
            if (atomic_load_explicit(
                    &task->head.is_suspended_sqe_exhaustion,
                    memory_order_acquire)) {
                awaiting_msg = "a non-write io_uring SQE";
            }
            else if (atomic_load_explicit(
                         &task->head.is_suspended_sqe_exhaustion_wr,
                         memory_order_acquire)) {
                awaiting_msg = "a write io_uring SQE";
            }
            printf(
                "*** Task %p running on executor %p currently suspended "
                "awaiting %s did not set a cancellation initiation routine and "
                "so will be asked to cancel the next time it resumes.\n",
                (void *)task,
                (void *)ex,
                awaiting_msg);
            fflush(stdout);
#endif
            // We will be handling cancellation without involving io_uring
            task->please_cancel_status = please_cancel_invoked_seen;
            atomic_unlock(&ex->lock);
            return monad_c_make_failure(EAGAIN);
        }
        // We will need to handle cancellation CQEs
        task->please_cancel_status = please_cancel_invoked_not_seen_yet;
        monad_c_result r = task->please_cancel(ex, task);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        char const *awaiting_msg = "i/o";
        char const *result_msg = "success";
        if (atomic_load_explicit(
                &task->head.is_suspended_sqe_exhaustion,
                memory_order_acquire)) {
            awaiting_msg = "a non-write io_uring SQE";
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_sqe_exhaustion_wr,
                     memory_order_acquire)) {
            awaiting_msg = "a write io_uring SQE";
        }
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
            result_msg = outcome_status_code_message(&r.error);
        }
        printf(
            "*** Task %p running on executor %p currently suspended "
            "awaiting %s initiated its cancellation which returned status "
            "'%s'. It has also been asked to cancel the next time it "
            "resumes.\n",
            (void *)task,
            (void *)ex,
            awaiting_msg,
            result_msg);
        fflush(stdout);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_VALUE(r)) {
            task->please_cancel_status = please_cancel_cancelled;
        }
        atomic_unlock(&ex->lock);
        return r;
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        if (atomic_load_explicit(
                &task->head.is_suspended_for_io, memory_order_acquire)) {
            // Have this return ECANCELED when it resumes
            task->head.derived.result = monad_c_make_failure(ECANCELED);
            task->please_cancel_status = please_cancel_invoked_not_seen_yet;
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Task %p running on executor %p currently pending "
                "resumption "
                "due to i/o completion will be told the i/o failed with "
                "ECANCELED.\n",
                (void *)task,
                (void *)ex);
            fflush(stdout);
#endif
            atomic_unlock(&ex->lock);
            return monad_c_make_success(0);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_io_buffer_exhaustion,
                     memory_order_acquire)) {
            // If this is true and is_suspended_awaiting is false, then the task
            // has been assigned an i/o buffer and is shortly about to be
            // resumed. In this case, request cancellation and do nothing else.
            task->please_cancel_status = please_cancel_invoked_not_seen_yet;
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Task %p running on executor %p currently pending "
                "resumption "
                "due to i/o buffer acquisition has been notified of "
                "cancellation.\n",
                (void *)task,
                (void *)ex);
            fflush(stdout);
#endif
            atomic_unlock(&ex->lock);
            return monad_c_make_success(0);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_max_concurrency,
                     memory_order_acquire)) {
            // If this is true and is_suspended_awaiting is false, then the task
            // has been is shortly about to be resumed. In this case, request
            // cancellation and do nothing else.
            task->please_cancel_status = please_cancel_invoked_not_seen_yet;
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Task %p running on executor %p currently pending "
                "resumption "
                "due to max concurrency has been notified of "
                "cancellation.\n",
                (void *)task,
                (void *)ex);
            fflush(stdout);
#endif
            atomic_unlock(&ex->lock);
            return monad_c_make_success(0);
        }
        abort();
    }
    else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Task %p running on executor %p is not cancellable as it is "
            "neither running nor suspended. Returning ENOENT.\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        atomic_unlock(&ex->lock);
        return monad_c_make_failure(ENOENT);
    }
    abort();
}

static monad_c_result monad_async_task_set_priorities_impl(
    struct monad_async_task_impl *task, monad_async_priority cpu,
    monad_async_priority io,
    int changing_io_buffer_awaiting_was_inserted_at_front)
{
    if (io != monad_async_priority_unchanged) {
        task->head.priority.io = io;
    }
    if (cpu == monad_async_priority_unchanged &&
        changing_io_buffer_awaiting_was_inserted_at_front == 0) {
        return monad_c_make_success(0);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    if (ex != nullptr) {
        if (atomic_load_explicit(
                &task->head.is_running, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_running[monad_async_task_effective_cpu_priority(
                    task)],
                task,
                &ex->head.tasks_running);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_awaiting, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_awaiting
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_completed,
                     memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_completed
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
        }
    }
    if (cpu != monad_async_priority_unchanged) {
        task->head.priority.cpu = cpu;
    }
    if (changing_io_buffer_awaiting_was_inserted_at_front < 0) {
        task->io_buffer_awaiting_was_inserted_at_front = false;
    }
    else if (changing_io_buffer_awaiting_was_inserted_at_front > 0) {
        task->io_buffer_awaiting_was_inserted_at_front = true;
    }
    if (ex != nullptr) {
        if (atomic_load_explicit(
                &task->head.is_running, memory_order_acquire)) {
            LIST_APPEND_ATOMIC_COUNTER(
                ex->tasks_running[monad_async_task_effective_cpu_priority(
                    task)],
                task,
                &ex->head.tasks_running);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_awaiting, memory_order_acquire)) {
            LIST_APPEND_ATOMIC_COUNTER(
                ex->tasks_suspended_awaiting
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_completed,
                     memory_order_acquire)) {
            LIST_APPEND_ATOMIC_COUNTER(
                ex->tasks_suspended_completed
                    [monad_async_task_effective_cpu_priority(task)],
                task,
                &ex->head.tasks_suspended);
        }
    }
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_set_priorities(
    monad_async_task task, monad_async_priority cpu, monad_async_priority io)
{
    return monad_async_task_set_priorities_impl(
        (struct monad_async_task_impl *)task, cpu, io, 0);
}

monad_c_result monad_async_task_io_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task != *(struct monad_async_task_impl **)&iostatus->result) {
        return monad_c_make_failure(ENOENT);
    }
    if (iostatus->cancel_ == nullptr) {
        return monad_c_make_failure(EAGAIN);
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

static inline monad_c_result monad_async_task_suspend_for_duration_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    struct io_uring_sqe *sqe = get_sqe_for_cancellation(ex);
    io_uring_prep_timeout_remove(
        sqe, (__u64)io_uring_mangle_into_data(task), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(task);
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

monad_c_result monad_async_task_suspend_for_duration(
    monad_async_io_status **completed, monad_async_task task_, uint64_t ns)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (ns != monad_async_duration_infinite_non_cancelling &&
        task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        return monad_c_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    // timespec must live until resumption
    struct __kernel_timespec ts;
    if (ns != monad_async_duration_infinite_non_cancelling ||
        completed == nullptr) {
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = true,
            .max_concurrent_io_pacing_already_done = false};
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, flags);
        if (sqe == nullptr) {
            assert(task->please_cancel_status != please_cancel_not_invoked);
            return monad_c_make_failure(ECANCELED);
        }
        if (ns == 0) {
            io_uring_prep_nop(sqe);
        }
        else {
            ts.tv_sec = (long long)(ns / 1000000000);
            ts.tv_nsec = (long long)(ns % 1000000000);
            io_uring_prep_timeout(sqe, &ts, 0, 0);
        }
        io_uring_sqe_set_data(sqe, task, task, nullptr);
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
    fflush(stdout);
#endif
    atomic_store_explicit(
        &task->head.is_suspended_for_io, true, memory_order_release);
    monad_c_result ret = monad_async_executor_suspend_impl(
        ex,
        task,
        monad_async_task_suspend_for_duration_cancel,
        completed,
        nullptr);
    assert(
        atomic_load_explicit(
            &task->head.is_suspended_for_io, memory_order_acquire) == true);
    atomic_store_explicit(
        &task->head.is_suspended_for_io, false, memory_order_release);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "suspend_for_duration *completed=%p\n",
        (void *)task,
        (void *)ex,
        completed ? (void *)*completed : nullptr);
    fflush(stdout);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        if (ns > 0 && outcome_status_code_equal_generic(&ret.error, ETIME)) {
            // io_uring returns timeouts as failure with ETIME, so
            // filter those out
            return monad_c_make_success(0);
        }
        return ret;
    }
    return monad_c_make_success(0);
}

// Returns true if an i/o buffer was detached and passed to a resumed task
static inline bool
monad_async_task_claim_registered_io_write_buffer_resume_task(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    bool const is_for_write, bool const is_large_page,
    bool resume_with_error_no_buffers_remaining)
{
    bool buffer_detached_and_passed = false;
    assert(
        ex->registered_buffers[is_for_write]
            .buffer[is_large_page]
            .tasks_awaiting.count > 0);
    assert(atomic_load_explicit(
        &task->head.is_suspended_io_buffer_exhaustion, memory_order_acquire));
    // Do NOT unset is_suspended_io_buffer_exhaustion here!!!
    LIST_REMOVE(
        ex->registered_buffers[is_for_write]
            .buffer[is_large_page]
            .tasks_awaiting,
        &task->io_buffer_awaiting,
        (size_t *)nullptr);

    assert(
        atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire) == true);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, false, memory_order_release);
    LIST_REMOVE(
        ex->tasks_suspended_awaiting[monad_async_task_effective_cpu_priority(
            task)],
        task,
        (size_t *)nullptr);

    task->head.ticks_when_suspended_completed =
        get_ticks_count(memory_order_relaxed);
    // Mark that this task was resumed due to i/o buffer await
    MONAD_CONTEXT_CHECK_RESULT(monad_async_task_set_priorities_impl(
        task,
        monad_async_priority_unchanged,
        monad_async_priority_unchanged,
        1));
    atomic_store_explicit(
        &task->head.is_suspended_completed, true, memory_order_release);
    // We need to ensure that the order of tasks being resumed matches the order
    // of suspension pending an i/o buffer, so insert at the right location. A
    // wrinkle here is that if there are other higher priority tasks than this
    // one, one of them may claim the free buffer before this one gets resumed.
    // To solve this, detach the buffer and use the result to smuggle it
    // through. To prevent i/o buffer starvation of higher priority work, we
    // also need to temporarily boost tasks given an i/o buffer so they execute
    // ASAP.
    if (resume_with_error_no_buffers_remaining) {
        task->head.derived.result = monad_c_make_failure(ENOBUFS);
        atomic_store_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            false,
            memory_order_release);
    }
    else if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        task->head.derived.result = monad_c_make_failure(ECANCELED);
        atomic_store_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            false,
            memory_order_release);
    }
    else {
        struct monad_async_executor_free_registered_buffer *p =
            ex->registered_buffers[is_for_write].buffer[is_large_page].free;
        // Use the result to pass through which buffer has just been freed
        task->head.derived.result = monad_c_make_success((intptr_t)p);
        ex->registered_buffers[is_for_write].buffer[is_large_page].free =
            p->next;
        buffer_detached_and_passed = true;
    }
    struct monad_async_task_impl *pos =
        ex->tasks_suspended_completed[monad_async_task_effective_cpu_priority(
                                          task)]
            .front;
    for (; pos != nullptr &&
           pos->io_buffer_awaiting_was_inserted_at_front == true;
         pos = pos->next) {
    }
    if (pos == nullptr) {
        LIST_APPEND(
            ex->tasks_suspended_completed
                [monad_async_task_effective_cpu_priority(task)],
            task,
            (size_t *)nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d tasks_awaiting.count=%zu at tail of resumption "
            "queue\n",
            (void *)ex,
            (void *)task,
            is_for_write,
            is_large_page,
            ex->registered_buffers[is_for_write]
                .buffer[is_large_page]
                .tasks_awaiting.count);
        fflush(stdout);
#endif
    }
    else if (
        pos ==
        ex->tasks_suspended_completed[monad_async_task_effective_cpu_priority(
                                          task)]
            .front) {
        LIST_PREPEND(
            ex->tasks_suspended_completed
                [monad_async_task_effective_cpu_priority(task)],
            task,
            (size_t *)nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d tasks_awaiting.count=%zu at front of resumption "
            "queue\n",
            (void *)ex,
            (void *)task,
            is_for_write,
            is_large_page,
            ex->registered_buffers[is_for_write]
                .buffer[is_large_page]
                .tasks_awaiting.count);
        fflush(stdout);
#endif
    }
    else {
        LIST_INSERT(
            ex->tasks_suspended_completed
                [monad_async_task_effective_cpu_priority(task)],
            pos,
            task,
            (size_t *)nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d tasks_awaiting.count=%zu at middle of resumption "
            "queue\n",
            (void *)ex,
            (void *)task,
            is_for_write,
            is_large_page,
            ex->registered_buffers[is_for_write]
                .buffer[is_large_page]
                .tasks_awaiting.count);
        fflush(stdout);
#endif
    }
    return buffer_detached_and_passed;
}

// Resume with just freed i/o buffer
static inline monad_c_result
monad_async_task_claim_registered_io_write_buffer_resume(
    struct monad_async_executor_impl *ex, bool const is_for_write,
    bool const is_large_page)
{
    struct monad_async_task_impl *task =
        (struct monad_async_task_impl *)((char *)ex
                                             ->registered_buffers[is_for_write]
                                             .buffer[is_large_page]
                                             .tasks_awaiting.front -
                                         offsetof(
                                             struct monad_async_task_impl,
                                             io_buffer_awaiting));
    assert(task->please_cancel_status == please_cancel_not_invoked);
    bool const buffer_detached_and_passed =
        monad_async_task_claim_registered_io_write_buffer_resume_task(
            ex, task, is_for_write, is_large_page, false);
    (void)buffer_detached_and_passed;
    assert(buffer_detached_and_passed);
    return monad_c_make_success(0);
}

static inline monad_c_result
monad_async_task_claim_registered_io_write_buffer_resume_with_error_no_buffers_remaining(
    struct monad_async_executor_impl *ex, bool const is_for_write,
    bool const is_large_page)
{
    struct monad_async_task_impl *task =
        (struct monad_async_task_impl *)((char *)ex
                                             ->registered_buffers[is_for_write]
                                             .buffer[is_large_page]
                                             .tasks_awaiting.front -
                                         offsetof(
                                             struct monad_async_task_impl,
                                             io_buffer_awaiting));
    assert(task->please_cancel_status == please_cancel_not_invoked);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p initiates resumption task %p awaiting i/o buffer due "
        "to i/o buffer deadlock is_for_write=%d is_large_page=%d "
        "tasks_awaiting.count=%zu\n",
        (void *)ex,
        (void *)task,
        task->io_buffer_awaiting_is_for_write,
        task->io_buffer_awaiting_is_for_large_page,
        ex->registered_buffers[task->io_buffer_awaiting_is_for_write]
            .buffer[task->io_buffer_awaiting_is_for_large_page]
            .tasks_awaiting.count);
    fflush(stdout);
#endif
    bool const buffer_detached_and_passed =
        monad_async_task_claim_registered_io_write_buffer_resume_task(
            ex, task, is_for_write, is_large_page, true);
    (void)buffer_detached_and_passed;
    assert(!buffer_detached_and_passed);
    ex->head.registered_buffers.total_deadlocks_broken++;
    return monad_c_make_success(0);
}

// Cancellation for tasks waiting on a registered i/o buffer
static inline monad_c_result
monad_async_task_claim_registered_io_write_buffer_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p initiates resumption task %p awaiting i/o buffer due "
        "to cancellation is_for_write=%d is_large_page=%d "
        "tasks_awaiting.count=%zu\n",
        (void *)ex,
        (void *)task,
        task->io_buffer_awaiting_is_for_write,
        task->io_buffer_awaiting_is_for_large_page,
        ex->registered_buffers[task->io_buffer_awaiting_is_for_write]
            .buffer[task->io_buffer_awaiting_is_for_large_page]
            .tasks_awaiting.count);
    fflush(stdout);
#endif
    assert(task->please_cancel_status != please_cancel_not_invoked);
    bool const buffer_detached_and_passed =
        monad_async_task_claim_registered_io_write_buffer_resume_task(
            ex,
            task,
            task->io_buffer_awaiting_is_for_write,
            task->io_buffer_awaiting_is_for_large_page,
            false);
    assert(!buffer_detached_and_passed);
    (void)buffer_detached_and_passed;
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

monad_c_result monad_async_task_claim_registered_file_io_write_buffer(
    monad_async_task_registered_io_buffer *buffer, monad_async_task task_,
    size_t bytes_requested,
    struct monad_async_task_claim_registered_io_buffer_flags flags)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        return monad_c_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    if (bytes_requested >
        ex->registered_buffers[!flags._for_read_ring].buffer[1].size) {
        assert(false);
        return monad_c_make_failure(EINVAL);
    }

    struct monad_async_executor_free_registered_buffer *p = nullptr;
    bool const is_large_page =
        (bytes_requested >
         ex->registered_buffers[!flags._for_read_ring].buffer[0].size);
    if (ex->registered_buffers[!flags._for_read_ring]
                .buffer[is_large_page]
                .free == nullptr ||
        ex->registered_buffers[!flags._for_read_ring]
                .buffer[is_large_page]
                .tasks_awaiting.count > 0) {
        if (flags.fail_dont_suspend ||
            ex->registered_buffers[!flags._for_read_ring].size == 0 ||
            ex->registered_buffers[!flags._for_read_ring].buffers[0].iov_len !=
                ex->registered_buffers[!flags._for_read_ring]
                    .buffer[is_large_page]
                    .size) {
            return monad_c_make_failure(ENOMEM);
        }
        atomic_store_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            true,
            memory_order_release);
        LIST_APPEND(
            ex->registered_buffers[!flags._for_read_ring]
                .buffer[is_large_page]
                .tasks_awaiting,
            &task->io_buffer_awaiting,
            (size_t *)nullptr);
        assert(task->io_buffer_awaiting_is_for_write == false);
        task->io_buffer_awaiting_is_for_write = !flags._for_read_ring;
        task->io_buffer_awaiting_is_for_large_page = is_large_page;
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p suspends task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d tasks_awaiting.count=%zu\n",
            (void *)ex,
            (void *)task,
            !flags._for_read_ring,
            is_large_page,
            ex->registered_buffers[!flags._for_read_ring]
                .buffer[is_large_page]
                .tasks_awaiting.count);
        fflush(stdout);
#endif
#ifndef NDEBUG
        if (ex->head.registered_buffers.total_released == 0) {
            fprintf(
                stderr,
                "WARNING: Task going to sleep waiting for an i/o buffer, but "
                "none have ever been released. Do you have enough i/o "
                "buffers?\n");
        }
#endif
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_async_executor_suspend_impl(
            ex,
            task,
            monad_async_task_claim_registered_io_write_buffer_cancel,
            nullptr,
            nullptr));
        // Unset this flag here, not when we removed this task from the list.
        // Otherwise cancellation cannot tell that this is a resumed task due to
        // i/o buffer exhaustion. Note if this is false, there is no attached
        // buffer being passed through
        bool const buffer_detached_and_passed = atomic_load_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            memory_order_acquire);
        atomic_store_explicit(
            &task->head.is_suspended_io_buffer_exhaustion,
            false,
            memory_order_release);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting i/o buffer "
            "is_for_write=%d "
            "is_large_page=%d io_buffer_awaiting_was_inserted_at_front=%d "
            "io_buffer_awaiting_is_for_write=%d "
            "io_buffer_awaiting_is_for_large_page=%d "
            "please_cancel_status=%d\n",
            (void *)ex,
            (void *)task,
            !flags._for_read_ring,
            is_large_page,
            task->io_buffer_awaiting_was_inserted_at_front,
            task->io_buffer_awaiting_is_for_write,
            task->io_buffer_awaiting_is_for_large_page,
            task->please_cancel_status);
        fflush(stdout);
#endif
        // This task no longer is resumed due to i/o buffer wait
        MONAD_CONTEXT_CHECK_RESULT(monad_async_task_set_priorities_impl(
            task,
            monad_async_priority_unchanged,
            monad_async_priority_unchanged,
            -1));
        task->io_buffer_awaiting_is_for_write = false;
        task->io_buffer_awaiting_is_for_large_page = false;
        p = (struct monad_async_executor_free_registered_buffer *)
                task->head.derived.result.value;
        if (buffer_detached_and_passed) {
            if (task->please_cancel_status != please_cancel_not_invoked) {
                if (task->please_cancel_status < please_cancel_invoked_seen) {
                    task->please_cancel_status = please_cancel_invoked_seen;
                }
                // If cancellation was invoked between the resumption of this
                // task with an attached buffer, that buffer will now need
                // freeing.
                assert(p != nullptr);
                // Keep counters correct
                ex->head.registered_buffers.total_claimed++;
                ex->head.registered_buffers.ticks_last_claim =
                    get_ticks_count(memory_order_relaxed);
                MONAD_CONTEXT_CHECK_RESULT(
                    monad_async_task_release_registered_io_buffer(
                        &task->head,
                        !flags._for_read_ring ? -(int)p->index
                                              : (int)p->index));
                return monad_c_make_failure(ECANCELED);
            }
        }
        else {
            if (task->please_cancel_status != please_cancel_not_invoked) {
                if (task->please_cancel_status < please_cancel_invoked_seen) {
                    task->please_cancel_status = please_cancel_invoked_seen;
                }
                // If cancellation was invoked before the resumption of this
                // task, result in this case will NOT contain the i/o buffer,
                // because
                // monad_async_task_claim_registered_io_write_buffer_resume_task()
                // will have seen that this task is being cancelled and will not
                // pass a buffer to me. Instead, result should have been set to
                // ECANCELED.
                assert(BOOST_OUTCOME_C_RESULT_HAS_ERROR(
                    task->head.derived.result));
                assert(task->head.derived.result.error.value == ECANCELED);
                return monad_c_make_failure(ECANCELED);
            }
            // Probably ENOBUFS
            return task->head.derived.result;
        }
        assert(p != nullptr);
        assert(buffer_detached_and_passed);
    }
    else {
        p = ex->registered_buffers[!flags._for_read_ring]
                .buffer[is_large_page]
                .free;
        ex->registered_buffers[!flags._for_read_ring]
            .buffer[is_large_page]
            .free = p->next;
    }
    buffer->index = !flags._for_read_ring ? -(int)p->index : (int)p->index;
    buffer->iov[0].iov_base = (void *)p;
    buffer->iov[0].iov_len = ex->registered_buffers[!flags._for_read_ring]
                                 .buffer[is_large_page]
                                 .size;
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p hands out registered i/o buffer %p is_for_write=%d "
        "is_large_page=%d\n",
        (void *)ex,
        (void *)p,
        !flags._for_read_ring,
        is_large_page);
    fflush(stdout);
#endif
    ex->head.registered_buffers.total_claimed++;
    ex->head.registered_buffers.ticks_last_claim =
        get_ticks_count(memory_order_relaxed);
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_claim_registered_socket_io_write_buffer(
    monad_async_task_registered_io_buffer *buffer, monad_async_task task,
    size_t bytes_requested,
    struct monad_async_task_claim_registered_io_buffer_flags flags)
{
    // Socket writes occur on the non-write ring!
    flags._for_read_ring = true;
    return monad_async_task_claim_registered_file_io_write_buffer(
        buffer, task, bytes_requested, flags);
}

monad_c_result monad_async_task_release_registered_io_buffer(
    monad_async_task task_, int buffer_index)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    bool const is_for_write = (buffer_index < 0);
    if (is_for_write) {
        buffer_index = -buffer_index;
    }
    if (buffer_index <= 0 ||
        (unsigned)buffer_index > ex->registered_buffers[is_for_write].size) {
        assert(false);
        return monad_c_make_failure(EINVAL);
    }
    struct iovec *iov =
        &ex->registered_buffers[is_for_write].buffers[buffer_index - 1];
    bool const is_large_page =
        (iov->iov_len > ex->registered_buffers[is_for_write].buffer[0].size);
    if (is_for_write ||
        (unsigned)buffer_index <=
            ex->registered_buffers[0].buffer[is_large_page].count -
                ex->registered_buffers[0]
                    .buffer[is_large_page]
                    .buf_ring_count) {
        struct monad_async_executor_free_registered_buffer *p =
            (struct monad_async_executor_free_registered_buffer *)iov->iov_base;
        p->index = (unsigned)buffer_index;
        p->next =
            ex->registered_buffers[is_for_write].buffer[is_large_page].free;
        ex->registered_buffers[is_for_write].buffer[is_large_page].free = p;
    }
    else {
        io_uring_buf_ring_add(
            ex->registered_buffers[0].buffer[is_large_page].buf_ring,
            ex->registered_buffers[0].buffers[buffer_index - 1].iov_base,
            (unsigned)ex->registered_buffers[0]
                .buffers[buffer_index - 1]
                .iov_len,
            (unsigned short)buffer_index,
            ex->registered_buffers[0].buffer[is_large_page].buf_ring_mask,
            0);
        // FIXME: Advancing per buffer release isn't efficient, it would be
        // better if this were batched. Equally, io_uring running out of free
        // buffers isn't good.
        io_uring_buf_ring_advance(
            ex->registered_buffers[0].buffer[is_large_page].buf_ring, 1);
    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p gets back registered i/o buffer %p is_for_write=%d "
        "is_large_page=%d will resume "
        "awaiting task=%p awaiting tasks=%zu\n",
        (void *)ex,
        (void *)iov->iov_base,
        is_for_write,
        is_large_page,
        (void *)(ex->registered_buffers[is_for_write]
                             .buffer[is_large_page]
                             .tasks_awaiting.count > 0
                     ? ex->registered_buffers[is_for_write]
                           .buffer[is_large_page]
                           .tasks_awaiting.front
                     : nullptr),
        ex->registered_buffers[is_for_write]
            .buffer[is_large_page]
            .tasks_awaiting.count);
    fflush(stdout);
#endif
    ex->head.registered_buffers.total_released++;
    monad_cpu_ticks_count_t const ticks_now =
        get_ticks_count(memory_order_relaxed);
    ex->registered_buffers[is_for_write].buffer[is_large_page].ticks_last_free =
        ticks_now;
    ex->head.registered_buffers.ticks_last_release = ticks_now;
    if (ex->registered_buffers[is_for_write]
            .buffer[is_large_page]
            .tasks_awaiting.count > 0) {
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            monad_async_task_claim_registered_io_write_buffer_resume(
                ex, is_for_write, is_large_page));
    }
    return monad_c_make_success(0);
}
