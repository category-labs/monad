#include "monad/async/task.h"

#include "executor.h"
#include "task_impl.h"

// #define MONAD_ASYNC_FIBER_PRINTING 1

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>

extern void monad_async_executor_task_detach(monad_context_task task);

monad_c_result monad_async_task_create(
    monad_async_task *task, monad_context_switcher switcher,
    struct monad_async_task_attr *attr)
{
    struct monad_async_task_impl *p = (struct monad_async_task_impl *)calloc(
        1, MONAD_CONTEXT_TASK_ALLOCATION_SIZE);
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->head.derived.detach = monad_async_executor_task_detach;
    p->head.io_recipient_task = (monad_async_task)p;
    p->head.priority.cpu = monad_async_priority_normal;
    p->head.priority.io = monad_async_priority_normal;
    monad_c_result r = switcher->create(
        &p->head.derived.context, switcher, &p->head.derived, &attr->derived);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        (void)monad_async_task_destroy((monad_async_task)p);
        return r;
    }
    atomic_store_explicit(
        &p->head.derived.context->switcher, switcher, memory_order_release);
    memcpy(p->magic, "MNASTASK", 8);
    *task = (monad_async_task)p;
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_suspend_save_detach_and_invoke(
    monad_async_task task_, monad_async_task opt_save,
    monad_c_result (*to_invoke)(monad_context_task detached_task))
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (opt_save != nullptr) {
        memcpy(
            ((char *)opt_save) + sizeof(struct monad_context_task_head),
            ((char *)task_) + sizeof(struct monad_context_task_head),
            sizeof(struct monad_async_task_head) -
                sizeof(struct monad_context_task_head));
    }
    monad_context_task context_task = &task_->derived;
    task->call_after_suspend_to_executor_data = nullptr;
    task->call_after_suspend_to_executor = to_invoke;
    monad_async_executor_task_detach(context_task);
    if (opt_save != nullptr) {
        opt_save->ticks_when_detached = task->head.ticks_when_detached;
        opt_save->total_ticks_executed = task->head.total_ticks_executed;
        atomic_store_explicit(
            &opt_save->is_running, false, memory_order_release);
        atomic_store_explicit(
            &opt_save->current_executor, nullptr, memory_order_release);
    }
    // Return to executor
    task->head.derived.result = monad_c_make_success(0);
    atomic_load_explicit(&context_task->context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(context_task->context, nullptr);
    return task->head.derived.result;
}

monad_async_task monad_async_task_from_foreign_context(
    monad_context_task context_task, monad_async_task opt_save)
{
    struct monad_async_task_impl *task =
        (struct monad_async_task_impl *)context_task;
    if (opt_save != nullptr) {
        memcpy(
            ((char *)task) + sizeof(struct monad_context_task_head),
            ((char *)opt_save) + sizeof(struct monad_context_task_head),
            sizeof(struct monad_async_task_head) -
                sizeof(struct monad_context_task_head));
    }
    else {
        memset(
            ((char *)task) + sizeof(struct monad_context_task_head),
            0,
            sizeof(struct monad_async_task_head) -
                sizeof(struct monad_context_task_head));
        task->head.io_recipient_task = (monad_async_task)context_task;
        task->head.priority.cpu = monad_async_priority_normal;
        task->head.priority.io = monad_async_priority_normal;
    }
    task->head.derived.detach = monad_async_executor_task_detach;
    memset(
        ((char *)task) + sizeof(struct monad_async_task_head),
        0,
        sizeof(struct monad_async_task_impl) -
            sizeof(struct monad_async_task_head));
    memcpy(task->magic, "MNASTASK", 8);
    return &task->head;
}

monad_c_result monad_async_task_destroy(monad_async_task task)
{
    struct monad_async_task_impl *p = (struct monad_async_task_impl *)task;
    if (atomic_load_explicit(&p->head.is_running, memory_order_acquire)) {
        fprintf(
            stderr,
            "FATAL: You cannot destroy a currently running task. Suspend or "
            "exit it first.\n");
        abort();
    }
    if (!monad_async_task_has_exited(task)) {
        monad_async_executor ex =
            atomic_load_explicit(&task->current_executor, memory_order_acquire);
        monad_c_result r = monad_async_task_cancel(ex, task);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
            if (!outcome_status_code_equal_generic(&r.error, ENOENT) &&
                !outcome_status_code_equal_generic(&r.error, EAGAIN)) {
                return r;
            }
        }
        while (!monad_async_task_has_exited(task)) {
            r = monad_async_executor_run(ex, 1, nullptr);
        }
    }
    memset(p->magic, 0, 8);
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
        atomic_load_explicit(
            &p->head.derived.context->switcher, memory_order_acquire)
            ->destroy(p->head.derived.context));
    free(task);
    return monad_c_make_success(0);
}
