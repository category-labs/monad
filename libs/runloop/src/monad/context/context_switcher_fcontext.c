// #define MONAD_CONTEXT_PRINTING 1
// #define MONAD_CONTEXT_DISABLE_GDB_IPC

#include "monad/context/context_switcher.h"

#include <errno.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <threads.h>

#include <monad-boost/context/fcontext.h>
#include <monad/core/tl_tid.h>

#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
    #include <gdb/linux-thread-db-user-threads.h>
#endif

#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>

#if MONAD_CONTEXT_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif
#if MONAD_CONTEXT_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
    #include <valgrind/valgrind.h>
#endif

monad_context_switcher_impl const monad_context_switcher_fcontext = {
    .create = monad_context_switcher_fcontext_create};

BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_fcontext_create(
    monad_context *context, monad_context_switcher switcher,
    monad_context_task task, const struct monad_context_task_attr *attr);
BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_fcontext_destroy(monad_context context);
static inline void monad_context_fcontext_suspend_and_call_resume(
    monad_context current_context, monad_context new_context);
static inline void monad_context_fcontext_resume(
    monad_context current_context, monad_context new_context);
BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_fcontext_resume_many(
    monad_context_switcher switcher,
    monad_c_result (*resumed)(
        void *user_ptr, monad_context fake_current_context),
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

struct monad_context_fcontext
{
    struct monad_context_head head;
    void *stack_storage;
    size_t stack_storage_size;

    monad_fcontext_t fctx; // the most recent suspension point
};

struct monad_context_switcher_fcontext
{
    struct monad_context_switcher_head head;
    thrd_t owning_thread;
    size_t within_resume_many;
    struct monad_context_fcontext
        fake_main_context; // used to indicate main resumed you
};

static inline monad_c_result
monad_context_switcher_fcontext_destroy(monad_context_switcher switcher)
{
    struct monad_context_switcher_fcontext *p =
        (struct monad_context_switcher_fcontext *)switcher;
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
    free(p);
    return monad_c_make_success(0);
}

monad_c_result
monad_context_switcher_fcontext_create(monad_context_switcher *switcher)
{
    struct monad_context_switcher_fcontext *p =
        (struct monad_context_switcher_fcontext *)calloc(
            1, sizeof(struct monad_context_switcher_fcontext));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    static const struct monad_context_switcher_head to_copy = {
        .contexts = 0,
        .self_destroy = monad_context_switcher_fcontext_destroy,
        .create = monad_context_fcontext_create,
        .destroy = monad_context_fcontext_destroy,
        .suspend_and_call_resume =
            monad_context_fcontext_suspend_and_call_resume,
        .resume = monad_context_fcontext_resume,
        .resume_many = monad_context_fcontext_resume_many};
    memcpy(&p->head, &to_copy, sizeof(to_copy));
    p->owning_thread = thrd_current();
    atomic_store_explicit(
        &p->fake_main_context.head.switcher, &p->head, memory_order_release);
#if MONAD_CONTEXT_HAVE_TSAN
    p->fake_main_context.head.sanitizer.fiber = __tsan_get_current_fiber();
#endif
    *switcher = (monad_context_switcher)p;
    return monad_c_make_success(0);
}

/*****************************************************************************/
#if MONAD_CONTEXT_HAVE_ASAN || MONAD_CONTEXT_HAVE_TSAN
static inline __attribute__((always_inline)) void start_switch_context(
    struct monad_context_head *dest_context, void **fake_stack_save,
    void const *bottom, size_t size)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom;
    (void)size;
    #if MONAD_CONTEXT_HAVE_ASAN
    __sanitizer_start_switch_fiber(fake_stack_save, bottom, size);
    #endif
    #if MONAD_CONTEXT_HAVE_TSAN
    __tsan_switch_to_fiber(dest_context->sanitizer.fiber, 0);
    #endif
}

static inline __attribute__((always_inline)) void finish_switch_context(
    struct monad_context_head *dest_context, void *fake_stack_save,
    void const **bottom_old, size_t *size_old)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom_old;
    (void)size_old;
    #if MONAD_CONTEXT_HAVE_ASAN
    __sanitizer_finish_switch_fiber(fake_stack_save, bottom_old, size_old);
    #endif
}
#else
static inline void
start_switch_context(struct monad_context_head *, void **, void const *, size_t)
{
}

static inline void finish_switch_context(
    struct monad_context_head *, void *, void const **, size_t *)
{
}
#endif

struct monad_context_fcontext_task_runner_args
{
    struct monad_context_fcontext *context;
    monad_context_task task;
};

static void
monad_context_fcontext_task_runner(struct monad_transfer_t creation_transfer)
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

    struct monad_context_fcontext *const context =
        ((struct monad_context_fcontext_task_runner_args *)
             creation_transfer.data)
            ->context;
    monad_context_task task =
        ((struct monad_context_fcontext_task_runner_args *)
             creation_transfer.data)
            ->task;
    struct monad_context_switcher_fcontext *switcher =
        (struct monad_context_switcher_fcontext *)atomic_load_explicit(
            &context->head.switcher, memory_order_acquire);
    switcher->fake_main_context.fctx = creation_transfer.fctx;
    creation_transfer.fctx = nullptr;
    creation_transfer.data = nullptr;

#if MONAD_CONTEXT_HAVE_ASAN
    // First time call fake_stack_save will be null which means no historical
    // stack to restore for this brand new context
    assert(context->head.sanitizer.fake_stack_save == nullptr);
#endif
    finish_switch_context(
        &context->head,
        context->head.sanitizer.fake_stack_save,
        &context->head.sanitizer.bottom,
        &context->head.sanitizer.size);
#if MONAD_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p launches\n",
        get_tl_tid(),
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
#if MONAD_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p suspends in base task runner "
            "awaiting code to run\n",
            get_tl_tid(),
            (void *)context);
        fflush(stdout);
#endif
        monad_context_fcontext_suspend_and_call_resume(&context->head, nullptr);
#if MONAD_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p resumes in base task runner, begins "
            "executing task.\n",
            get_tl_tid(),
            (void *)context);
        fflush(stdout);
#endif
#ifndef NDEBUG
        switcher =
            (struct monad_context_switcher_fcontext *)atomic_load_explicit(
                &context->head.switcher, memory_order_acquire);
        if (switcher->owning_thread != thrd_current()) {
            fprintf(
                stderr,
                "FATAL: Context being switched on a kernel thread different to "
                "the assigned context switcher.\n");
            abort();
        }
#endif
#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
        userspace_thread_db_userspace_thread_info_t *ti =
            get_thread_db_userspace_thread_info(~context->head.thread_db_slot);
        ti->startfunc = (void (*)(void))task->user_code;
        set_thread_db_userspace_thread_running_nonlocking(
            ~context->head.thread_db_slot, get_tl_tid());
#endif
        // Execute the task
        context->head.is_running = true;
        task->result = task->user_code(task);
        context->head.is_running = false;
#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
        set_thread_db_userspace_thread_exited_nonlocking(
            ~context->head.thread_db_slot);
#endif
#if MONAD_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p returns to base task runner, task "
            "has "
            "exited\n",
            get_tl_tid(),
            (void *)context);
        fflush(stdout);
#endif
        task->detach(task);
    }
}

static monad_c_result monad_context_fcontext_create(
    monad_context *context, monad_context_switcher switcher_,
    monad_context_task task, const struct monad_context_task_attr *attr)
{
    struct monad_context_switcher_fcontext *switcher =
        (struct monad_context_switcher_fcontext *)switcher_;
    struct monad_context_fcontext *p = (struct monad_context_fcontext *)calloc(
        1, sizeof(struct monad_context_fcontext));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
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
        monad_c_result ret = monad_c_make_failure(errno);
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
#if MONAD_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p is given stack between %p-%p with "
        "guard "
        "page at %p\n",
        get_tl_tid(),
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
#if MONAD_CONTEXT_HAVE_TSAN
    p->head.sanitizer.fiber = __tsan_create_fiber(0);
#endif
    // Launch execution, suspending immediately
    monad_fcontext_t old_fake_main_context_fctx =
        switcher->fake_main_context.fctx;
    p->fctx = monad_make_fcontext(
        stack_base, stack_size, monad_context_fcontext_task_runner);
    start_switch_context(
        &p->head,
        &switcher->fake_main_context.head.sanitizer.fake_stack_save,
        p->head.sanitizer.bottom,
        p->head.sanitizer.size);
    struct monad_context_fcontext_task_runner_args args = {
        .context = p, .task = task};
    p->fctx = monad_jump_fcontext(p->fctx, &args).fctx;
    finish_switch_context(
        switcher->fake_main_context.head.sanitizer.fiber,
        switcher->fake_main_context.head.sanitizer.fake_stack_save,
        nullptr,
        nullptr);
    switcher->fake_main_context.fctx = old_fake_main_context_fctx;
    *context = (monad_context)p;
    atomic_store_explicit(&p->head.switcher, nullptr, memory_order_release);
    monad_context_reparent_switcher(*context, switcher_);
#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
    userspace_thread_db_userspace_thread_info_t *ti =
        get_thread_db_userspace_thread_info(~(*context)->thread_db_slot);
    ti->stack_sp = stack_base;
    ti->stack_size = stack_size;
    LINUX_THREAD_DB_USER_THREADS_SHUTUP_TSAN_LOCK_UNLOCK;
#endif
    return monad_c_make_success(0);
}

static monad_c_result monad_context_fcontext_destroy(monad_context context)
{
    struct monad_context_fcontext *p = (struct monad_context_fcontext *)context;
#if MONAD_CONTEXT_HAVE_TSAN
    if (p->head.sanitizer.fiber != nullptr) {
        __tsan_destroy_fiber(p->head.sanitizer.fiber);
        p->head.sanitizer.fiber = nullptr;
    }
#endif
    if (p->stack_storage != nullptr) {
#if MONAD_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p is destroyed\n",
            get_tl_tid(),
            (void *)context);
        fflush(stdout);
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
        VALGRIND_STACK_DEREGISTER(p->head.sanitizer.valgrind_stack_id);
#endif
        size_t const page_size = (size_t)getpagesize();
        if (munmap(p->stack_storage, p->stack_storage_size + page_size) == -1) {
            return monad_c_make_failure(errno);
        }
        p->stack_storage = nullptr;
    }
    monad_context_reparent_switcher(context, nullptr);
#if MONAD_ASYNC_GUARD_PAGE_JMPBUF
    munmap(p, sizeof(struct monad_context_fcontext));
#else
    free(context);
#endif
    return monad_c_make_success(0);
}

static void monad_context_fcontext_suspend_and_call_resume(
    monad_context current_context, monad_context new_context)
{
    struct monad_context_fcontext *p =
        (struct monad_context_fcontext *)current_context;
#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
    if (current_context->is_running && current_context->thread_db_slot != 0) {
        userspace_thread_db_userspace_thread_info_t *ti =
            get_thread_db_userspace_thread_info(
                ~current_context->thread_db_slot);
        USERSPACE_THREAD_SET_FROM_HERE(ti);
        set_thread_db_userspace_thread_suspended_nonlocking(
            ~current_context->thread_db_slot, ti);
    }
#endif
    if (new_context == nullptr) {
        monad_context_fcontext_resume(
            current_context,
            &((struct monad_context_switcher_fcontext *)atomic_load_explicit(
                  &p->head.switcher, memory_order_acquire))
                 ->fake_main_context.head);
        return;
    }
    struct monad_context_switcher_fcontext *new_context_switcher =
        (struct monad_context_switcher_fcontext *)atomic_load_explicit(
            &new_context->switcher, memory_order_acquire);
    struct monad_context_switcher_fcontext *current_switcher =
        (struct monad_context_switcher_fcontext *)atomic_load_explicit(
            &p->head.switcher, memory_order_acquire);
    if (new_context_switcher == current_switcher) {
        // We are transferring between contexts on the same context switcher,
        // which enables a fast path.
        monad_context_fcontext_resume(current_context, new_context);
        return;
    }
    // Otherwise, we use the slow path.
    abort(); // TODO FIXME
    /* What we need to do:

    1. Transfer back to main context.
    2. Have main context then invoke resume on the foreign context switcher.

    OR:

    Investigate if setjmp/longjmp can be used here, it would be faster and
    more convenient than vectoring through the main context.
    */

    // Call resume on the destination switcher
    atomic_load_explicit(&new_context->switcher, memory_order_acquire)
        ->resume(current_context, new_context);
    // Some switchers return, and that's okay
}

static void monad_context_fcontext_resume(
    monad_context current_context, monad_context new_context)
{
    assert(current_context != new_context);
    assert(
        atomic_load_explicit(
            &current_context->switcher, memory_order_acquire) ==
        atomic_load_explicit(&new_context->switcher, memory_order_acquire));
    struct monad_context_fcontext *p =
        (struct monad_context_fcontext *)new_context;
#if MONAD_CONTEXT_PRINTING
    {
        struct monad_context_switcher_fcontext *switcher =
            (struct monad_context_switcher_fcontext *)atomic_load_explicit(
                &p->head.switcher, memory_order_acquire);
        printf(
            "*** %d: Execution context %p initiates resumption of execution in "
            "context %p (fctx = %p, is main context = %d)\n",
            get_tl_tid(),
            (void *)current_context,
            (void *)new_context,
            (void *)p->fctx,
            &switcher->fake_main_context.head == new_context);
        fflush(stdout);
    }
#endif
    start_switch_context(
        &p->head,
        &current_context->sanitizer.fake_stack_save,
        new_context->sanitizer.bottom,
        new_context->sanitizer.size);
    current_context->is_suspended = true;
    struct monad_transfer_t transfer =
        monad_jump_fcontext(p->fctx, current_context);
    // He has resumed
    current_context->is_suspended = false;
    finish_switch_context(
        current_context,
        current_context->sanitizer.fake_stack_save,
        &current_context->sanitizer.bottom,
        &current_context->sanitizer.size);
    struct monad_context_fcontext *source_context =
        (struct monad_context_fcontext *)transfer.data;
    source_context->fctx = transfer.fctx;
#ifndef MONAD_CONTEXT_DISABLE_GDB_IPC
    if (current_context->is_running &&
        &((struct monad_context_switcher_fcontext *)atomic_load_explicit(
              &current_context->switcher, memory_order_acquire))
                ->fake_main_context.head != current_context) {
        set_thread_db_userspace_thread_running_nonlocking(
            ~current_context->thread_db_slot, get_tl_tid());
    }
#endif
#if MONAD_CONTEXT_PRINTING
    {
        printf(
            "*** %d: Execution context %p has resumed execution from context "
            "%p which has been saved as %p\n",
            get_tl_tid(),
            (void *)current_context,
            (void *)source_context,
            (void *)transfer.fctx);
        fflush(stdout);
    }
#endif
}

static monad_c_result monad_context_fcontext_resume_many(
    monad_context_switcher switcher_,
    monad_c_result (*resumed)(void *user_ptr, monad_context just_suspended),
    void *user_ptr)
{
    struct monad_context_switcher_fcontext *switcher =
        (struct monad_context_switcher_fcontext *)switcher_;
    switcher->within_resume_many++;
    monad_fcontext_t old_fake_main_context_fctx =
        switcher->fake_main_context.fctx;
#if MONAD_CONTEXT_PRINTING
    printf(
        "*** %d: Resume many entry saves current main context %p\n",
        get_tl_tid(),
        (void *)old_fake_main_context_fctx);
    fflush(stdout);
#endif
    monad_c_result r = resumed(user_ptr, &switcher->fake_main_context.head);
#if MONAD_CONTEXT_PRINTING
    printf(
        "*** %d: Resume many exit replaces current main context %p with saved "
        "main context %p\n",
        get_tl_tid(),
        (void *)switcher->fake_main_context.fctx,
        (void *)old_fake_main_context_fctx);
    fflush(stdout);
#endif
    switcher->fake_main_context.fctx = old_fake_main_context_fctx;
    switcher->within_resume_many--;
    return r;
}
