#include "monad/async/task.h"

#include "monad/async/boost_result.h"
#include "task_impl.h"

// #define MONAD_ASYNC_FIBER_PRINTING 1

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>

extern void monad_async_executor_task_detach(monad_async_task task);

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
            if (!outcome_status_code_equal_generic(&r.error, ENOENT)) {
                return r;
            }
        }
    }
    memset(p->magic, 0, 8);
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
        atomic_load_explicit(&p->context->switcher, memory_order_acquire)
            ->destroy(p->context));
    free(task);
    return monad_async_make_success(0);
}
