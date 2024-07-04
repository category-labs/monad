#include "current.h"
#include "assert.h"
#include <pthread.h>
#include <setjmp.h>
#include <threads.h>
#include <unistd.h>

#if defined(MONAD_USE_TSAN)
    #include <sanitizer/tsan_interface.h>
#endif

extern thread_local monad_fiber_t monad_fiber_main_fiber_;

extern int pthread_getname_np(pthread_t thread, char *name, size_t size);

monad_fiber_t *monad_fiber_main()
{
    MONAD_DEBUG_ASSERT(monad_fiber_main_fiber_.context != NULL);
    return &monad_fiber_main_fiber_;
}

extern thread_local monad_fiber_t *monad_fiber_current_;

void monad_fiber_init_main()
{
    if (monad_fiber_main_fiber_.context == NULL) {
        monad_fiber_main_fiber_.scheduler = monad_fiber_scheduler_current();
        monad_fiber_main_fiber_.context = monad_fiber_main_context();
#if defined(MONAD_USE_TSAN)
        monad_fiber_main_fiber_.context->tsan_fiber =
            __tsan_get_current_fiber();
#endif
        //+monad_fiber_main_fiber_.scheduler = scheduler;
        char buffer[256];

        if (0 == pthread_getname_np(pthread_self(), buffer, 256ull)) {
            monad_fiber_set_name(monad_fiber_main_context(), buffer);
        }
        // MONAD_DEBUG_ASSERT(monad_fiber_main_fiber_.context->fiber == NULL);
    }

    MONAD_DEBUG_ASSERT(
        monad_fiber_current_ == NULL ||
        monad_fiber_current_ == &monad_fiber_main_fiber_);
    monad_fiber_current_ = &monad_fiber_main_fiber_;
}

extern thread_local monad_fiber_t *monad_fiber_current_;

monad_fiber_t *monad_fiber_current()
{
    MONAD_DEBUG_ASSERT(monad_fiber_current_ != NULL);
    return monad_fiber_current_;
}

monad_fiber_t *monad_fiber_activate_fiber(monad_fiber_t *new_current)
{
    monad_fiber_t *pre = monad_fiber_current();
    monad_fiber_current_ = new_current;
    return pre;
}

void monad_fiber_switch_to_fiber(monad_fiber_t *target)
{
    MONAD_DEBUG_ASSERT(target != NULL);
    MONAD_DEBUG_ASSERT(target->context != NULL);
    MONAD_DEBUG_ASSERT(target->context->fiber != NULL);
    monad_fiber_t *pre = monad_fiber_current();
    // LOG here
    (void)monad_fiber_context_switch(pre->context, target->context);

    monad_fiber_activate_fiber(pre);
}

struct monad_fiber_switch_to_fiber_with_impl_arg
{
    void (*func)(void *);
    void *arg;
};

static monad_fiber_context_t *
monad_fiber_switch_to_fiber_with_impl(monad_fiber_context_t *ctx, void *arg_)
{
    struct monad_fiber_switch_to_fiber_with_impl_arg arg =
        *(struct monad_fiber_switch_to_fiber_with_impl_arg *)arg_;
    arg.func(arg.arg);
    return ctx;
}

void monad_fiber_switch_to_fiber_with(
    monad_fiber_t *target, void (*func)(void *), void *arg)
{
    MONAD_DEBUG_ASSERT(target != NULL);
    MONAD_DEBUG_ASSERT(target->context != NULL);
    MONAD_DEBUG_ASSERT(target->context->fiber != NULL);
    monad_fiber_t *pre = monad_fiber_current();

    monad_fiber_activate_fiber(target);
    struct monad_fiber_switch_to_fiber_with_impl_arg arg_ = {func, arg};

    (void)monad_fiber_context_switch_with(
        pre->context,
        target->context,
        &monad_fiber_switch_to_fiber_with_impl,
        &arg_);

    monad_fiber_activate_fiber(pre);
}

void monad_fiber_switch_to_main()
{
    // LOG here
    monad_fiber_switch_to_fiber(monad_fiber_main());
}

void monad_fiber_yield()
{
    monad_fiber_t *cc = monad_fiber_current();
    MONAD_ASSERT(cc->scheduler != NULL);
    monad_fiber_task_t *t = monad_fiber_scheduler_pop_higher_priority_task(
        cc->scheduler,
        cc->task.priority + 1 /* so we also yield if it's he same priority */);
    if (t == NULL) {
        return; // no work, no problem
    }
    t->resume(
        t); // if this is a fiber, the context switch will be done in here.
}

struct monad_fiber_await_impl_t
{
    monad_fiber_t *fiber;
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/);
    void *arg;
};

static monad_fiber_context_t *
monad_fiber_await_impl(monad_fiber_context_t *from, void *ptr)
{
    struct monad_fiber_await_impl_t impl =
        *(struct monad_fiber_await_impl_t *)ptr;
    monad_fiber_activate_fiber(impl.fiber);
    (*impl.suspend_to)(impl.fiber, impl.arg);
    return from;
}

void monad_fiber_await(
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/), void *arg)
{
    monad_fiber_t *from = monad_fiber_current();
    MONAD_ASSERT(!monad_fiber_is_main(from));

    struct monad_fiber_await_impl_t impl = {
        .fiber = from, .suspend_to = suspend_to, .arg = arg};

    monad_fiber_context_switch_with(
        from->context,
        monad_fiber_main()->context,
        &monad_fiber_await_impl,
        &impl);
    monad_fiber_activate_fiber(from);
}

struct monad_fiber_create_arg_t
{
    void *arg;
    void (*func)(void *);

    monad_fiber_t **res;
    monad_fiber_scheduler_t *sched;
};

struct monad_fiber_impl
{
    monad_fiber_t base;
    jmp_buf exit_jmp;
};

static void monad_fiber_create_impl_resume(monad_fiber_task_t *task)
{
    // note this doesn't post yet. the resumer must take care of this!
    monad_fiber_switch_to_fiber((monad_fiber_t *)task);
}

static monad_fiber_context_t *
monad_fiber_create_impl_destroy_impl(monad_fiber_context_t *ctx, void *buf)
{
    // ASAN check goes here.
#if defined(MONAD_USE_ASAN)
    monad_fiber_finish_switch(
        &monad_fiber_current()->context->asan, &ctx->asan);
#endif

    longjmp(buf, 1);
    return ctx;
}

static void monad_fiber_create_impl_destroy(monad_fiber_task_t *task)
{
    struct monad_fiber_impl *impl = (struct monad_fiber_impl *)task;

    if (impl->base.context->fiber == NULL) { // we're in the context
        longjmp(((struct monad_fiber_impl *)task)->exit_jmp, 1);
    }
    else { // must context_switch first!
        monad_fiber_context_switch_with(
            monad_fiber_current()->context,
            impl->base.context,
            &monad_fiber_create_impl_destroy_impl,
            &impl->exit_jmp);
    }
}

monad_fiber_context_t *monad_fiber_create_impl(
    void *arg_, monad_fiber_context_t *fiber, monad_fiber_context_t * /*from*/)
{
    struct monad_fiber_create_arg_t *arg =
        (struct monad_fiber_create_arg_t *)arg_;
    monad_fiber_t **ff = arg->res;

    void (*func)(void *) = arg->func;
    void *func_arg = arg->arg;
    struct monad_fiber_impl f = {
        .base = {
            .context = fiber,
            .scheduler = arg->sched,
            .task = {
                .resume = &monad_fiber_create_impl_resume,
                .destroy = &monad_fiber_create_impl_destroy,
                .priority = 0}}};
    *ff = &f.base;

    monad_fiber_activate_fiber(*ff);

    if (!setjmp(f.exit_jmp)) {
        func(func_arg);
    }

    monad_fiber_activate_fiber(monad_fiber_main());
    return monad_fiber_main()->context;
}

monad_fiber_t *monad_fiber_create(
    size_t stack_size, bool protected_stack, monad_fiber_scheduler_t *scheduler,
    void func(void *), void *arg)
{
    monad_fiber_t *res = NULL;
    struct monad_fiber_create_arg_t monad_fiber_create_arg = {
        .arg = arg, .func = func, .res = &res, .sched = scheduler};
    monad_fiber_context_t *ctx = monad_fiber_context_callcc(
        monad_fiber_main()->context,
        stack_size,
        protected_stack,
        &monad_fiber_create_impl,
        &monad_fiber_create_arg);

    monad_fiber_activate_fiber(monad_fiber_main());

    //
    if (res != NULL && ctx != NULL) {
        if (res->context == NULL) { // it might have been set internally already
            res->context = ctx;
        }
    }
    else {
        return NULL;
    }

    return res;
}

bool monad_fiber_in_fiber()
{
    return !monad_fiber_is_main(monad_fiber_current());
}
