// #define MONAD_ASYNC_CONTEXT_PRINTING 1

#include "monad/async/context_switcher.h"

#include "monad/async/task.h"

extern void monad_async_executor_task_detach(monad_async_task task);
#include <stdio.h>
#include <string.h>
#include <threads.h>

#include <monad-boost/context/fcontext.h>

#include <sys/mman.h>
#include <sys/resource.h>

#if MONAD_ASYNC_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
    #include <valgrind/valgrind.h>
#endif

monad_async_context_switcher_impl const monad_async_context_switcher_fcontext =
    {.create = monad_async_context_switcher_fcontext_create};

BOOST_OUTCOME_C_NODISCARD static inline monad_async_result
monad_async_context_fcontext_create(
    monad_async_context *context, monad_async_context_switcher switcher,
    monad_async_task task, const struct monad_async_task_attr *attr);
BOOST_OUTCOME_C_NODISCARD static inline monad_async_result
monad_async_context_fcontext_destroy(monad_async_context context);
static inline void monad_async_context_fcontext_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context);
static inline void monad_async_context_fcontext_resume(
    monad_async_context current_context, monad_async_context new_context);
BOOST_OUTCOME_C_NODISCARD static inline monad_async_result
monad_async_context_fcontext_resume_many(
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

struct monad_async_context_fcontext
{
    struct monad_async_context_head head;
    void *stack_storage;
    size_t stack_storage_size;
    monad_async_task task;

    monad_fcontext_t fctx;

    struct
    {
        monad_async_context context;
        struct monad_transfer_t transfer;
    } resumer;
};

struct monad_async_context_switcher_fcontext
{
    struct monad_async_context_switcher_head head;
    thrd_t owning_thread;
    size_t within_resume_many;
    struct monad_async_context_fcontext *last_suspended;
    struct monad_async_context_fcontext fake_main_context;

    struct
    {
        char stack_storage[1024];
        monad_fcontext_t fctx;
    } suspend_never;
};

static void monad_async_context_switcher_fcontext_suspend_never_runner(
    struct monad_transfer_t back_to_creator)
{
    // This fcontext resumes everything which resumes it
    // This lets fcontexts save themselves at a point in time.
    for (;;) {
        back_to_creator =
            monad_jump_fcontext(back_to_creator.fctx, back_to_creator.data);
    }
}

static inline monad_async_result monad_async_context_switcher_fcontext_destroy(
    monad_async_context_switcher switcher)
{
    struct monad_async_context_switcher_fcontext *p =
        (struct monad_async_context_switcher_fcontext *)switcher;
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

monad_async_result monad_async_context_switcher_fcontext_create(
    monad_async_context_switcher *switcher)
{
    struct monad_async_context_switcher_fcontext *p =
        (struct monad_async_context_switcher_fcontext *)calloc(
            1, sizeof(struct monad_async_context_switcher_fcontext));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    static const struct monad_async_context_switcher_head to_copy = {
        .contexts = 0,
        .self_destroy = monad_async_context_switcher_fcontext_destroy,
        .create = monad_async_context_fcontext_create,
        .destroy = monad_async_context_fcontext_destroy,
        .suspend_and_call_resume =
            monad_async_context_fcontext_suspend_and_call_resume,
        .resume = monad_async_context_fcontext_resume,
        .resume_many = monad_async_context_fcontext_resume_many};
    memcpy(&p->head, &to_copy, sizeof(to_copy));
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    if (thrd_success != mtx_init(&p->head.contexts_list.lock, mtx_plain)) {
        abort();
    }
#endif
    p->owning_thread = thrd_current();
    atomic_store_explicit(
        &p->fake_main_context.head.switcher, &p->head, memory_order_release);
    p->suspend_never.fctx = monad_make_fcontext(
        p->suspend_never.stack_storage + sizeof(p->suspend_never.stack_storage),
        sizeof(p->suspend_never.stack_storage),
        monad_async_context_switcher_fcontext_suspend_never_runner);
#if MONAD_ASYNC_HAVE_TSAN
    p->fake_main_context.head.sanitizer.fiber = __tsan_get_current_fiber();
#endif
    *switcher = (monad_async_context_switcher)p;
    return monad_async_make_success(0);
}

/*****************************************************************************/
#if MONAD_ASYNC_HAVE_ASAN || MONAD_ASYNC_HAVE_TSAN
static inline __attribute__((always_inline)) void start_switch_context(
    struct monad_async_context_head *dest_context, void **fake_stack_save,
    void const *bottom, size_t size)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom;
    (void)size;
    #if MONAD_ASYNC_HAVE_ASAN
    __sanitizer_start_switch_fiber(fake_stack_save, bottom, size);
    #endif
    #if MONAD_ASYNC_HAVE_TSAN
    __tsan_switch_to_fiber(dest_context->sanitizer.fiber, 0);
    #endif
}

static inline __attribute__((always_inline)) void finish_switch_context(
    struct monad_async_context_head *dest_context, void *fake_stack_save,
    void const **bottom_old, size_t *size_old)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom_old;
    (void)size_old;
    #if MONAD_ASYNC_HAVE_ASAN
    __sanitizer_finish_switch_fiber(fake_stack_save, bottom_old, size_old);
    #endif
}
#else
static inline void start_switch_context(
    struct monad_async_context_head *, void **, void const *, size_t)
{
}

static inline void finish_switch_context(
    struct monad_async_context_head *, void *, void const **, size_t *)
{
}
#endif

static void monad_async_context_fcontext_task_runner(
    struct monad_transfer_t back_to_creator)
{
    // We are now at the base of our custom stack
    //
    // WARNING: This custom stack will get freed without unwind
    // This is why when not in use, it sits at the jump in this base runner
    // function
    //
    // TODO: We currently don't tell the sanitiser to free its resources
    // associated with this context upon deallocation. For this, we need to
    // call:
    //
    // start_switch_context(nullptr, ret->sanitizer.bottom,
    // ret->sanitizer.size);
    //
    // just before the final jump out.

    struct monad_async_context_fcontext *context =
        (struct monad_async_context_fcontext *)back_to_creator.data;
    context->resumer.transfer = back_to_creator;
    monad_async_task task = context->task;

#if MONAD_ASYNC_HAVE_ASAN
    // First time call fake_stack_save will be null which means no historical
    // stack to restore for this brand new context
    assert(context->head.sanitizer.fake_stack_save == nullptr);
#endif
    finish_switch_context(
        &context->head,
        context->head.sanitizer.fake_stack_save,
        &context->head.sanitizer.bottom,
        &context->head.sanitizer.size);
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p launches\n",
        gettid(),
        (void *)context);
    fflush(stdout);
#endif
    size_t const page_size = (size_t)getpagesize();
    void *stack_base = (void *)((uintptr_t)context->stack_storage +
                                context->stack_storage_size + page_size);
    void *stack_front = (void *)((uintptr_t)context->stack_storage + page_size);
    (void)stack_base;
    (void)stack_front;
    for (;;) {
        // Tell the Linux kernel that this stack can be lazy reclaimed if there
        // is memory pressure
        madvise(
            stack_front, context->stack_storage_size - page_size, MADV_FREE);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p suspends in base task runner "
            "awaiting code to run\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
        monad_async_context_fcontext_suspend_and_call_resume(
            &context->head, nullptr);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p resumes in base task runner, begins "
            "executing task.\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
#ifndef NDEBUG
        struct monad_async_context_switcher_fcontext *switcher =
            (struct monad_async_context_switcher_fcontext *)
                atomic_load_explicit(
                    &context->head.switcher, memory_order_acquire);
        if (switcher->owning_thread != thrd_current()) {
            fprintf(
                stderr,
                "FATAL: Context being switched on a kernel thread different to "
                "the assigned context switcher.\n");
            abort();
        }
#endif
        // Execute the task
        task->result = task->user_code(task);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p returns to base task runner, task "
            "has "
            "exited\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
        monad_async_executor_task_detach(task);
    }
}

static monad_async_result monad_async_context_fcontext_create(
    monad_async_context *context, monad_async_context_switcher switcher_,
    monad_async_task task, const struct monad_async_task_attr *attr)
{
    struct monad_async_context_switcher_fcontext *switcher =
        (struct monad_async_context_switcher_fcontext *)switcher_;
    struct monad_async_context_fcontext *p =
        (struct monad_async_context_fcontext *)calloc(
            1, sizeof(struct monad_async_context_fcontext));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    atomic_store_explicit(&p->head.switcher, switcher_, memory_order_release);
    size_t const page_size = (size_t)getpagesize();
    size_t stack_size = (attr->stack_size + page_size - 1) & ~(page_size - 1);
    if (stack_size == 0) {
        stack_size = get_rlimit_stack();
    }
    p->stack_storage = mmap(
        nullptr,
        stack_size + page_size,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS,
        -1,
        0);
    if (p->stack_storage == MAP_FAILED) {
        monad_async_result ret = monad_async_make_failure(errno);
        p->stack_storage = nullptr;
        if (errno == ENOMEM) {
            fprintf(
                stderr,
                "NOTE: if mmap() fails to allocate a stack, and there is "
                "plenty of memory free, the cause is the Linux kernel VMA "
                "region limit being hit whereby no process may allocate more "
                "than 64k mmaps. You can safely raise vm.max_map_count = "
                "1048576 if needed.\n");
        }
        return ret;
    }
    p->stack_storage_size = stack_size;
    void *stack_base =
        (void *)((uintptr_t)p->stack_storage + stack_size + page_size);
    void *stack_front = (void *)((uintptr_t)p->stack_storage + page_size);
    (void)stack_front;
    // Put guard page at the front
    mmap(
        p->stack_storage,
        page_size,
        PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED | MAP_NORESERVE,
        -1,
        0);
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p is given stack between %p-%p with "
        "guard "
        "page at %p\n",
        gettid(),
        (void *)p,
        (void *)stack_front,
        (void *)stack_base,
        (void *)p->stack_storage);
    fflush(stdout);
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
    p->head.sanitizer.valgrind_stack_id =
        VALGRIND_STACK_REGISTER(stack_front, stack_base);
#endif
#if MONAD_ASYNC_HAVE_TSAN
    p->head.sanitizer.fiber = __tsan_create_fiber(0);
#endif
    // Launch execution, suspending immediately
    p->fctx = monad_make_fcontext(
        stack_base, stack_size, monad_async_context_fcontext_task_runner);
    start_switch_context(
        &p->head,
        &switcher->fake_main_context.head.sanitizer.fake_stack_save,
        p->head.sanitizer.bottom,
        p->head.sanitizer.size);
    p->task = task;
    p->resumer.context = &switcher->fake_main_context.head;
    p->fctx = monad_jump_fcontext(p->fctx, p).fctx;
    finish_switch_context(
        switcher->fake_main_context.head.sanitizer.fiber,
        switcher->fake_main_context.head.sanitizer.fake_stack_save,
        nullptr,
        nullptr);
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    p->head.stack_top = stack_base;
    p->head.stack_bottom = stack_front;
#endif
    *context = (monad_async_context)p;
    atomic_store_explicit(&p->head.switcher, nullptr, memory_order_release);
    monad_async_context_reparent_switcher(*context, switcher_);
    return monad_async_make_success(0);
}

static monad_async_result
monad_async_context_fcontext_destroy(monad_async_context context)
{
    struct monad_async_context_fcontext *p =
        (struct monad_async_context_fcontext *)context;
#if MONAD_ASYNC_HAVE_TSAN
    if (p->head.sanitizer.fiber != nullptr) {
        __tsan_destroy_fiber(p->head.sanitizer.fiber);
        p->head.sanitizer.fiber = nullptr;
    }
#endif
    if (p->stack_storage != nullptr) {
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p is destroyed\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
        VALGRIND_STACK_DEREGISTER(p->head.sanitizer.valgrind_stack_id);
#endif
        size_t const page_size = (size_t)getpagesize();
        if (munmap(p->stack_storage, p->stack_storage_size + page_size) == -1) {
            return monad_async_make_failure(errno);
        }
        p->stack_storage = nullptr;
    }
    monad_async_context_reparent_switcher(context, nullptr);
#if MONAD_ASYNC_GUARD_PAGE_JMPBUF
    munmap(p, sizeof(struct monad_async_context_fcontext));
#else
    free(context);
#endif
    return monad_async_make_success(0);
}

static void monad_async_context_fcontext_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context)
{
    struct monad_async_context_fcontext *p =
        (struct monad_async_context_fcontext *)current_context;
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    p->head.stack_current = __builtin_frame_address(0);
#endif
    if (new_context == nullptr) {
        // In the other context switchers, this means "return to normal
        // execution" i.e. the main context. fcontext doesn't really have such a
        // concept, so we have each fcontext store who resumed it and we define
        // "return to normal execution" as "return to whomever resumed me". We
        // save and restore `resume_transfer` around every context switch so
        // this should eventually result in resuming the main context
        struct monad_async_context_fcontext *p =
            (struct monad_async_context_fcontext *)current_context;
#if MONAD_ASYNC_CONTEXT_PRINTING
        {
            printf(
                "*** %d: Execution context %p initiates resumption of "
                "execution in main? context %p\n",
                gettid(),
                (void *)current_context,
                (void *)p->resumer.context);
            fflush(stdout);
        }
#endif
        start_switch_context(
            p->resumer.context,
            &current_context->sanitizer.fake_stack_save,
            p->resumer.context->sanitizer.bottom,
            p->resumer.context->sanitizer.size);
        p->resumer.transfer =
            monad_jump_fcontext(p->resumer.transfer.fctx, p->resumer.context);
        // He has resumed
        finish_switch_context(
            current_context,
            current_context->sanitizer.fake_stack_save,
            &current_context->sanitizer.bottom,
            &current_context->sanitizer.size);
        assert(p == p->resumer.transfer.data);
        return;
    }
    struct monad_async_context_switcher_fcontext *new_context_switcher =
        (struct monad_async_context_switcher_fcontext *)atomic_load_explicit(
            &new_context->switcher, memory_order_acquire);
    struct monad_async_context_switcher_fcontext *current_switcher =
        (struct monad_async_context_switcher_fcontext *)atomic_load_explicit(
            &p->head.switcher, memory_order_acquire);
    if (new_context_switcher == current_switcher) {
        // We are transferring between contexts on the same context switcher,
        // which enables a fast path
        monad_async_context_fcontext_resume(current_context, new_context);
        return;
    }
    // Otherwise, we use the slow path. We switch context to the suspend never
    // context to save our current state, then invoke the foreign context
    // switcher
    // No start_switch_context here
    struct monad_transfer_t ret =
        monad_jump_fcontext(current_switcher->suspend_never.fctx, nullptr);
    if (ret.data != nullptr) {
        // He has resumed
        finish_switch_context(
            current_context,
            current_context->sanitizer.fake_stack_save,
            &current_context->sanitizer.bottom,
            &current_context->sanitizer.size);
        assert(p == ret.data);
        p->resumer.transfer = ret;
        return;
    }
    p->fctx = ret.fctx;
    // Set last suspended
    struct monad_async_context_switcher_fcontext *switcher =
        (struct monad_async_context_switcher_fcontext *)atomic_load_explicit(
            &p->head.switcher, memory_order_acquire);
    switcher->last_suspended = p;
    // Call resume on the destination switcher
    atomic_load_explicit(&new_context->switcher, memory_order_acquire)
        ->resume(current_context, new_context);
    // Some switchers return, and that's okay
}

static void monad_async_context_fcontext_resume(
    monad_async_context current_context, monad_async_context new_context)
{
    assert(
        atomic_load_explicit(
            &current_context->switcher, memory_order_acquire) ==
        atomic_load_explicit(&new_context->switcher, memory_order_acquire));
    struct monad_async_context_fcontext *p =
        (struct monad_async_context_fcontext *)new_context;
#if MONAD_ASYNC_CONTEXT_PRINTING
    {
        printf(
            "*** %d: Execution context %p initiates resumption of execution in "
            "context %p\n",
            gettid(),
            (void *)current_context,
            (void *)new_context);
        fflush(stdout);
    }
#endif
    start_switch_context(
        &p->head,
        &current_context->sanitizer.fake_stack_save,
        new_context->sanitizer.bottom,
        new_context->sanitizer.size);
    // Set who is resuming you, and resume new context.
    p->resumer.context = current_context;
    struct monad_transfer_t ret = monad_jump_fcontext(p->fctx, p);
    p->fctx = ret.fctx;
    // He has resumed
    finish_switch_context(
        current_context,
        current_context->sanitizer.fake_stack_save,
        &current_context->sanitizer.bottom,
        &current_context->sanitizer.size);
    assert(current_context == ret.data);
}

static monad_async_result monad_async_context_fcontext_resume_many(
    monad_async_context_switcher switcher_,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context just_suspended),
    void *user_ptr)
{
    struct monad_async_context_switcher_fcontext *switcher =
        (struct monad_async_context_switcher_fcontext *)switcher_;
    switcher->last_suspended = nullptr;
    switcher->within_resume_many++;
    monad_async_result r = resumed(user_ptr, &switcher->fake_main_context.head);
    switcher->within_resume_many--;
    return r;
}
