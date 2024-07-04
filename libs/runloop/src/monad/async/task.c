#include "monad/async/task.h"

#include "task_impl.h"

// #define MONAD_ASYNC_FIBER_PRINTING 1

#include "monad_fiber/scheduler.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

extern void monad_async_executor_task_detach(monad_async_task task);

static void
monad_fiber_task_from_async_task_compute_resume(struct monad_fiber_task *const);

monad_async_result monad_async_task_create(
    monad_async_task *task, monad_async_context_switcher switcher,
    struct monad_async_task_attr *attr)
{
    struct monad_async_task_impl *p = (struct monad_async_task_impl *)calloc(
        1, sizeof(struct monad_async_task_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    p->head.io_recipient_task = (monad_async_task)p;
    p->head.priority.cpu = monad_async_priority_normal;
    p->head.priority.io = monad_async_priority_normal;
    monad_async_result r =
        switcher->create(&p->context, switcher, &p->head, attr);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        (void)monad_async_task_destroy((monad_async_task)p);
        return r;
    }
    atomic_store_explicit(
        &p->context->switcher, switcher, memory_order_release);
    p->fiber_task.resume = monad_fiber_task_from_async_task_compute_resume;
    memcpy(p->magic, "MNASTASK", 8);
    *task = (monad_async_task)p;
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_destroy(monad_async_task task)
{
    struct monad_async_task_impl *p = (struct monad_async_task_impl *)task;
    if (atomic_load_explicit(&p->head.is_running, memory_order_acquire)) {
        fprintf(
            stderr,
            "FATAL: You cannot destroy a currently running task. Suspend or "
            "exit it first.\n");
        abort();
    }
    monad_async_executor ex =
        atomic_load_explicit(&task->current_executor, memory_order_acquire);
    if (ex != nullptr) {
        monad_async_result r = monad_async_task_cancel(ex, task);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
            if (r.error.value != ENOENT) {
                return r;
            }
        }
    }
    memset(p->magic, 0, 8);
    MONAD_ASYNC_TRY_RESULT(
        ,
        atomic_load_explicit(&p->context->switcher, memory_order_acquire)
            ->destroy(p->context));
    free(task);
    return monad_async_make_success(0);
}

/***************************************************************************/

static monad_async_result monad_fiber_task_from_async_task_compute_resume_impl(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct monad_async_task_impl *task =
        (struct monad_async_task_impl *)user_ptr;
    if (task->fiber_task_please_resume_as_foreign_executor) {
#if MONAD_ASYNC_FIBER_PRINTING
        printf(
            "*** %d: monad fiber task begins/resumes execution of task %p on "
            "foreign "
            "executor.\n",
            gettid(),
            (void *)task);
        fflush(stdout);
#endif
        atomic_store_explicit(
            &task->head.is_running_on_foreign_executor,
            true,
            memory_order_release);
        task->fiber_task_please_resume_as_foreign_executor = false;
        monad_async_context_switcher switcher = atomic_load_explicit(
            &task->context->switcher, memory_order_acquire);
        switcher->resume(fake_current_context, task->context);
        // He may return from resume(), or he may call this function again
    }
    if (atomic_load_explicit(
            &task->head.is_running_on_foreign_executor, memory_order_acquire)) {
#if MONAD_ASYNC_FIBER_PRINTING
        printf(
            "*** %d: monad fiber task has completed suspending execution of "
            "task %p on foreign "
            "executor.\n",
            gettid(),
            (void *)task);
        fflush(stdout);
#endif
        if (task->call_after_suspend_to_executor != nullptr) {
            monad_async_result (*call_after_suspend_to_executor)(
                struct monad_async_task_impl *task) =
                task->call_after_suspend_to_executor;
            task->call_after_suspend_to_executor = nullptr;
            return call_after_suspend_to_executor(task);
        }
        return monad_async_make_success(0);
    }
    else if (!monad_async_task_has_exited(&task->head)) {
        fprintf(
            stderr,
            "FATAL: monad_fiber_task->resume() called on task currently "
            "attached to an i/o executor.\n");
        abort();
    }
    else {
#if MONAD_ASYNC_FIBER_PRINTING
        printf(
            "*** %d: monad fiber task exits execution of task %p on foreign "
            "executor.\n",
            gettid(),
            (void *)task);
        fflush(stdout);
#endif
        // Task has exited
        if (task->fiber_task.resume ==
            monad_fiber_task_from_async_task_compute_resume) {
            task->fiber_task.resume = nullptr;
        }
        atomic_store_explicit(
            &task->head.is_running_on_foreign_executor,
            false,
            memory_order_release);
    }
    return monad_async_make_success(0);
}

// This is what monad_fiber_task->resume() calls, it resumes execution of the
// context at its last suspension point
static void monad_fiber_task_from_async_task_compute_resume(
    struct monad_fiber_task *const fiber_task)
{
    struct monad_async_task_impl *task =
        (struct monad_async_task_impl *)monad_async_task_from_fiber_task(
            fiber_task);
    if (task->head.user_code == nullptr) {
        fprintf(
            stderr,
            "FATAL: monad_fiber_task->resume() called on task whose user_code "
            "task entry point function has not been set.\n");
        abort();
    }
    task->fiber_task_please_resume_as_foreign_executor = true;
    monad_async_context_switcher switcher =
        atomic_load_explicit(&task->context->switcher, memory_order_acquire);
    monad_async_result r = switcher->resume_many(
        switcher, monad_fiber_task_from_async_task_compute_resume_impl, task);
    MONAD_ASYNC_CHECK_RESULT(r);
}

struct monad_fiber_task *monad_fiber_task_from_async_task(monad_async_task task)
{
    struct monad_async_task_impl *p = (struct monad_async_task_impl *)task;
    return &p->fiber_task;
}

monad_async_task monad_async_task_from_fiber_task(struct monad_fiber_task *task)
{
    return (
        monad_async_task)((uintptr_t)task -
                          offsetof(struct monad_async_task_impl, fiber_task));
}

//

struct monad_fiber_resume_on_io_executor_call_after_suspend_to_executor_data
{
    monad_async_executor executor;
    monad_async_context_switcher opt_reparent_switcher;
};

static monad_async_result
monad_fiber_resume_on_io_executor_call_after_suspend_to_executor(
    struct monad_async_task_impl *task)
{
    // We are currently running on the compute executor
    struct monad_fiber_resume_on_io_executor_call_after_suspend_to_executor_data
        *data =
            (struct
             monad_fiber_resume_on_io_executor_call_after_suspend_to_executor_data
                 *)task->call_after_suspend_to_executor_data;
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task attaches task %p to native executor %p.\n",
        gettid(),
        (void *)task,
        (void *)data->executor);
    fflush(stdout);
#endif
    // We need to prevent monad_async_task_has_exited() temporarily returning
    // true. We also need is_running_on_foreign_executor to be false otherwise
    // there would be a race.
    //
    // Temporarily setting is_awaiting_dispatch gets the job done. Admittedly
    // it is hacky.
    atomic_store_explicit(
        &task->head.is_awaiting_dispatch, true, memory_order_release);
    atomic_store_explicit(
        &task->head.is_running_on_foreign_executor,
        false,
        memory_order_release);
    monad_async_result r = monad_async_task_attach(
        data->executor, &task->head, data->opt_reparent_switcher);
    atomic_store_explicit(
        &task->head.is_awaiting_dispatch, false, memory_order_release);
    return r;
}

monad_async_result monad_fiber_resume_on_io_executor(
    monad_async_executor executor, monad_async_task task_,
    monad_async_context_switcher opt_reparent_switcher)
{
    // We are currently running within the task context on the compute executor
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (!atomic_load_explicit(
            &task->head.is_running_on_foreign_executor, memory_order_acquire)) {
        fprintf(
            stderr,
            "FATAL: monad_fiber_resume_on_io_executor() called from not a "
            "foreign executor.\n");
        abort();
    }
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task suspends execution of task %p on foreign "
        "executor to initiate resume on native executor %p.\n",
        gettid(),
        (void *)task,
        (void *)executor);
    fflush(stdout);
#endif
    struct monad_fiber_resume_on_io_executor_call_after_suspend_to_executor_data
        data = {
            .executor = executor,
            .opt_reparent_switcher = opt_reparent_switcher};
    task->call_after_suspend_to_executor_data = &data;
    task->call_after_suspend_to_executor =
        monad_fiber_resume_on_io_executor_call_after_suspend_to_executor;
    task->head.ticks_when_suspended_awaiting =
        get_ticks_count(memory_order_relaxed);
    atomic_load_explicit(&task->context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(task->context, nullptr);
    task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task has resumed execution of task %p on native "
        "executor %p.\n",
        gettid(),
        (void *)task,
        (void *)executor);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}

//

struct
    monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor_data
{
    struct monad_fiber_scheduler *scheduler;
    int64_t priority;
    monad_async_context_switcher opt_reparent_switcher;
};

static monad_async_result
monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor(
    struct monad_async_task_impl *task)
{
    // We are currently running in the i/o executor run loop
    struct monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor_data
        *data =
            (struct
             monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor_data
                 *)task->call_after_suspend_to_executor_data;
    if (data->opt_reparent_switcher != nullptr) {
        monad_async_context_reparent_switcher(
            task->context, data->opt_reparent_switcher);
    }
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task post task %p to foreign executor %p.\n",
        gettid(),
        (void *)task,
        (void *)data->scheduler);
    fflush(stdout);
#endif
    monad_fiber_scheduler_post(
        data->scheduler, monad_fiber_task_from_async_task(&task->head));
    return monad_async_make_success(0);
}

monad_async_result monad_fiber_resume_on_compute_executor(
    struct monad_fiber_scheduler *scheduler, monad_async_task task_,
    int64_t priority, monad_async_context_switcher opt_reparent_switcher)
{
    // We are currently running within the task context on the i/o executor
    monad_async_executor_task_detach(task_);
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task suspends execution of task %p on native "
        "executor to initiate resume on foreign executor %p.\n",
        gettid(),
        (void *)task,
        (void *)scheduler);
    fflush(stdout);
#endif
    // Need to set this, otherwise monad_async_task_has_exited() would return
    // true
    atomic_store_explicit(
        &task->head.is_running_on_foreign_executor, true, memory_order_release);
    struct
        monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor_data
            data = {
                .scheduler = scheduler,
                .priority = priority,
                .opt_reparent_switcher = opt_reparent_switcher};
    task->call_after_suspend_to_executor_data = &data;
    task->call_after_suspend_to_executor =
        monad_fiber_resume_on_compute_executor_call_after_suspend_to_executor;
    task->head.ticks_when_suspended_awaiting =
        get_ticks_count(memory_order_relaxed);
    atomic_load_explicit(&task->context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(task->context, nullptr);
    task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_FIBER_PRINTING
    printf(
        "*** %d: monad fiber task has resumed execution of task %p on foreign "
        "executor %p.\n",
        gettid(),
        (void *)task,
        (void *)scheduler);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}
