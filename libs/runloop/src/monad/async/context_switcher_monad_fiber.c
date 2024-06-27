// #define MONAD_ASYNC_CONTEXT_PRINTING 1

#include "monad/async/context_switcher.h"

#include "monad/async/task.h"

extern void monad_async_executor_task_detach(monad_async_task task);

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>

#include <sys/resource.h>
#include <unistd.h>

#include <monad/fiber/context.h>

monad_async_context_switcher_impl const monad_async_context_switcher_fiber = {
    .create = monad_async_context_switcher_fiber_create};

MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_fiber_create(
    monad_async_context *context, monad_async_context_switcher switcher,
    monad_async_task task, const struct monad_async_task_attr *attr);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_fiber_destroy(monad_async_context context);
static inline void monad_async_context_fiber_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context);
static inline void monad_async_context_fiber_resume(
    monad_async_context current_context, monad_async_context new_context);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_fiber_resume_many(
    monad_async_context_switcher switcher,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context fake_current_context),
    void *user_ptr);

static inline size_t get_rlimit_stack()
{
    static size_t v;
    if (v != 0) {
        return v;
    }
    struct rlimit r = {0, 0};
    getrlimit(RLIMIT_STACK, &r);
    if (r.rlim_cur == 0 || r.rlim_cur == RLIM_INFINITY) {
        r.rlim_cur = 2 * 1024 * 1024;
    }
    v = (size_t)r.rlim_cur;
    return v;
}

struct monad_async_context_fiber
{
    struct monad_async_context_head head;
    bool please_exit;
    monad_fiber_context_t *fiber;
};

struct monad_async_context_switcher_fiber
{
    struct monad_async_context_switcher_head head;
    size_t within_resume_many;
    pid_t within_resume_many_tid;
    struct monad_async_context_fiber *last_suspended;
    struct monad_async_context_fiber resume_many_context;
};

static inline monad_async_result monad_async_context_switcher_fiber_destroy(
    monad_async_context_switcher switcher)
{
    struct monad_async_context_switcher_fiber *p =
        (struct monad_async_context_switcher_fiber *)switcher;
    unsigned contexts =
        atomic_load_explicit(&p->head.contexts, memory_order_acquire);
    if (contexts != 0) {
        fprintf(
            stderr,
            "FATAL: Context switcher destroyed whilst %u contexts still using "
            "it.\n",
            contexts);
        abort();
    }
    assert(!p->within_resume_many);
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    mtx_destroy(&p->head.contexts_list.lock);
#endif
    free(p);
    return monad_async_make_success(0);
}

monad_async_result monad_async_context_switcher_fiber_create(
    monad_async_context_switcher *switcher)
{
    struct monad_async_context_switcher_fiber *p =
        (struct monad_async_context_switcher_fiber *)calloc(
            1, sizeof(struct monad_async_context_switcher_fiber));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    static const struct monad_async_context_switcher_head to_copy = {
        .contexts = 0,
        .self_destroy = monad_async_context_switcher_fiber_destroy,
        .create = monad_async_context_fiber_create,
        .destroy = monad_async_context_fiber_destroy,
        .suspend_and_call_resume =
            monad_async_context_fiber_suspend_and_call_resume,
        .resume = monad_async_context_fiber_resume,
        .resume_many = monad_async_context_fiber_resume_many};
    memcpy(&p->head, &to_copy, sizeof(to_copy));
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    if (thrd_success != mtx_init(&p->head.contexts_list.lock, mtx_plain)) {
        abort();
    }
#endif
    p->resume_many_context.fiber = monad_fiber_main_context();
    atomic_store_explicit(
        &p->resume_many_context.head.switcher, &p->head, memory_order_release);
    *switcher = (monad_async_context_switcher)p;
    return monad_async_make_success(0);
}

/*****************************************************************************/
struct monad_async_context_fiber_task_runner_info_t
{
    monad_async_task const task;
    struct monad_async_context_fiber *context;
    struct monad_async_context_switcher_fiber *switcher;
};

static monad_fiber_context_t *monad_async_context_fiber_task_runner(
    void *info_, monad_fiber_context_t *me, monad_fiber_context_t *)
{
    // Immediately take a copy, as it will disappear
    struct monad_async_context_fiber_task_runner_info_t info =
        *(struct monad_async_context_fiber_task_runner_info_t *)info_;
    info.context->fiber = me;
    for (;;) {
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** Execution context %p suspends in base task runner "
            "awaiting code to run\n",
            (void *)info.context);
        fflush(stdout);
#endif
        assert(info.switcher->within_resume_many);
        monad_async_context_fiber_suspend_and_call_resume(
            &info.context->head, &info.switcher->resume_many_context.head);
        struct monad_async_context_switcher_fiber *newswitcher =
            (struct monad_async_context_switcher_fiber *)atomic_load_explicit(
                &info.context->head.switcher, memory_order_acquire);
        bool const task_has_been_moved_between_switchers =
            (newswitcher != info.switcher);
        (void)task_has_been_moved_between_switchers;
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p resumes in base task runner, begins "
            "executing task. task_has_been_moved_between_switchers=%d\n",
            gettid(),
            (void *)info.context,
            task_has_been_moved_between_switchers);
        fflush(stdout);
#endif
        info.switcher = newswitcher;
        if (info.context->please_exit) {
            // This causes fiber resource deallocation
            info.context->fiber = nullptr;
            return info.switcher->resume_many_context.fiber;
        }
        // Execute the task
        info.task->result = info.task->user_code(info.task);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** Execution context %p returns to base task runner, task has "
            "exited\n",
            (void *)info.context);
        fflush(stdout);
#endif
        monad_async_executor_task_detach(info.task);
    }
}

static monad_async_result monad_async_context_fiber_create(
    monad_async_context *context, monad_async_context_switcher switcher_,
    monad_async_task task, const struct monad_async_task_attr *attr)
{
    struct monad_async_context_switcher_fiber *switcher =
        (struct monad_async_context_switcher_fiber *)switcher_;
    struct monad_async_context_fiber *p =
        (struct monad_async_context_fiber *)calloc(
            1, sizeof(struct monad_async_context_fiber));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    atomic_store_explicit(&p->head.switcher, switcher_, memory_order_release);
    size_t stack_size = attr->stack_size;
    if (stack_size == 0) {
        stack_size = get_rlimit_stack();
    }
    struct monad_async_context_fiber_task_runner_info_t info = {
        .task = task, .context = p, .switcher = switcher};
    switcher->within_resume_many++;
    if (monad_fiber_context_callcc(
            monad_fiber_main_context(),
            stack_size,
            true,
            monad_async_context_fiber_task_runner,
            &info) == nullptr) {
        int const ec = errno;
        switcher->within_resume_many--;
        (void)monad_async_context_fiber_destroy((monad_async_context)p);
        return monad_async_make_failure(ec);
    }
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    // There is a size_t after p->fiber which is the allocated stack size
    p->head.stack_top = p->fiber;
    p->head.stack_bottom =
        (char *)p->fiber -
        *(size_t *)((char *)p->fiber + sizeof(monad_fiber_context_t));
#endif
    switcher->within_resume_many--;
    *context = (monad_async_context)p;
    atomic_store_explicit(&p->head.switcher, nullptr, memory_order_release);
    monad_async_context_reparent_switcher(*context, &switcher->head);
    return monad_async_make_success(0);
}

static monad_async_result
monad_async_context_fiber_destroy(monad_async_context context)
{
    struct monad_async_context_fiber *p =
        (struct monad_async_context_fiber *)context;
    if (p->fiber != nullptr) {
        struct monad_async_context_switcher_fiber *switcher =
            (struct monad_async_context_switcher_fiber *)atomic_load_explicit(
                &p->head.switcher, memory_order_acquire);
        p->please_exit = true;
        monad_async_context_fiber_resume(
            &switcher->resume_many_context.head, context);
        assert(p->fiber == nullptr);
        monad_async_context_reparent_switcher(context, nullptr);
    }
    free(context);
    return monad_async_make_success(0);
}

static void monad_async_context_fiber_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context)
{
    struct monad_async_context_fiber *p =
        (struct monad_async_context_fiber *)current_context;
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    p->head.stack_current = __builtin_frame_address(0);
#endif
    // Set last suspended
    struct monad_async_context_switcher_fiber *switcher =
        (struct monad_async_context_switcher_fiber *)atomic_load_explicit(
            &p->head.switcher, memory_order_acquire);
    switcher->last_suspended = p;
    if (new_context != nullptr) {
        // Call resume on the destination switcher
        atomic_load_explicit(&new_context->switcher, memory_order_acquire)
            ->resume(current_context, new_context);
        // Some switchers return, and that's okay
    }
    else {
        // Return to base
        monad_async_context_fiber_resume(
            current_context, &switcher->resume_many_context.head);
    }
}

static void monad_async_context_fiber_resume(
    monad_async_context current_context, monad_async_context new_context)
{
#if MONAD_ASYNC_CONTEXT_PRINTING
    struct monad_async_context_switcher_fiber *switcher =
        (struct monad_async_context_switcher_fiber *)atomic_load_explicit(
            &new_context->switcher, memory_order_acquire);
    bool new_context_is_resume_all_context =
        (new_context == &switcher->resume_many_context.head);
    printf(
        "*** Execution context %p initiates resumption of execution in context "
        "%p (is_resume_many_context = %d)\n",
        (void *)current_context,
        (void *)new_context,
        new_context_is_resume_all_context);
    fflush(stdout);
#endif
    monad_fiber_context_t *from =
        ((struct monad_async_context_fiber *)current_context)->fiber;
    monad_fiber_context_t *to =
        ((struct monad_async_context_fiber *)new_context)->fiber;
    monad_fiber_context_switch(from, to);
}

static monad_async_result monad_async_context_fiber_resume_many(
    monad_async_context_switcher switcher_,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context just_suspended),
    void *user_ptr)
{
    struct monad_async_context_switcher_fiber *switcher =
        (struct monad_async_context_switcher_fiber *)switcher_;
    switcher->last_suspended = nullptr;
    pid_t const mytid = gettid(),
                within_resume_many_tid = switcher->within_resume_many_tid;
    if (within_resume_many_tid != 0 && within_resume_many_tid != mytid) {
        fprintf(
            stderr,
            "FATAL: tid %d is currently within "
            "monad_async_context_fiber_resume_many and I tid %d is trying to "
            "do the same.\n",
            within_resume_many_tid,
            mytid);
        abort();
    }
    switcher->within_resume_many_tid = mytid;
    if (switcher->within_resume_many++ > 0) {
        fprintf(
            stderr,
            "FATAL: Nested monad_async_context_fiber_resume_many() not "
            "implemented.\n");
        abort();
    }
    monad_async_result r =
        resumed(user_ptr, &switcher->resume_many_context.head);
    switcher->within_resume_many--;
    switcher->within_resume_many_tid = 0;
    return r;
}
