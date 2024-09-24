#include "context_switcher.h"

#include <monad/linked_list_impl_common.h>

#include <gdb/linux-thread-db-user-threads.h>

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

LINUX_THREAD_DB_USER_THREADS_ATOMIC(thread_db_userspace_threads_t *)
_thread_db_userspace_threads[4];

static void __attribute__((constructor)) _thread_db_userspace_threads_init()
{
    assert(_thread_db_userspace_threads[0] == nullptr);
    size_t bytes = 4096; // enough for 63 items
    void *mem = malloc(bytes);
    if (mem != nullptr) {
        expand_thread_db_userspace_threads(&mem, &bytes);
    }
    else {
        // fprintf() may not be available yet, but abort() will be
        abort();
    }
}

static void _thread_db_userspace_threads_do_free(
    LINUX_THREAD_DB_USER_THREADS_ATOMIC(thread_db_userspace_threads_t *) *
    v_addr)
{
    thread_db_userspace_threads_t *v =
        LINUX_THREAD_DB_USER_THREADS_ATOMIC_LOAD(*v_addr);
    if (v != nullptr) {
        LINUX_THREAD_DB_USER_THREADS_ATOMIC_STORE(*v_addr, nullptr);
        free(v);
    }
}

static void __attribute__((destructor)) _thread_db_userspace_threads_free()
{
    _thread_db_userspace_threads_do_free(&_thread_db_userspace_threads[3]);
    _thread_db_userspace_threads_do_free(&_thread_db_userspace_threads[2]);
    _thread_db_userspace_threads_do_free(&_thread_db_userspace_threads[1]);
    _thread_db_userspace_threads_do_free(&_thread_db_userspace_threads[0]);
}

static size_t
_thread_db_userspace_thread_allocate_thread_db_userspace_thread_index()
{
    size_t thread_db_slot = allocate_thread_db_userspace_thread_index();
    while ((size_t)-1 == thread_db_slot) {
        thread_db_userspace_threads_t *current =
            LINUX_THREAD_DB_USER_THREADS_ATOMIC_LOAD(
                _thread_db_userspace_threads[0]);
        size_t bytes = current->total_bytes << 1;
        void *mem = malloc(bytes);
        if (mem == nullptr) {
            fprintf(stderr, "FATAL: Failed to expand thread_db storage\n");
            abort();
        }
        expand_thread_db_userspace_threads(&mem, &bytes);
        if (mem != nullptr) {
            free(mem);
        }
        thread_db_slot = allocate_thread_db_userspace_thread_index();
    }
    return thread_db_slot;
}

monad_context_switcher_impl const monad_context_switcher_none = {
    .create = monad_context_switcher_none_create};

BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_none_create(
    monad_context *context, monad_context_switcher switcher,
    monad_context_task task, const struct monad_context_task_attr *attr);
BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_none_destroy(monad_context context);
static inline void monad_context_none_suspend_and_call_resume(
    monad_context current_context, monad_context new_context);
static inline void monad_context_none_resume(
    monad_context current_context, monad_context new_context);
BOOST_OUTCOME_C_NODISCARD static inline monad_c_result
monad_context_none_resume_many(
    monad_context_switcher switcher,
    monad_c_result (*resumed)(void *user_ptr, monad_context just_suspended),
    void *user_ptr);

static inline monad_c_result
monad_context_switcher_none_destroy(monad_context_switcher p)
{
    unsigned contexts =
        atomic_load_explicit(&p->contexts, memory_order_acquire);
    if (contexts != 0) {
        fprintf(
            stderr,
            "FATAL: Context switcher destroyed whilst %u contexts still using "
            "it.\n",
            contexts);
        abort();
    }
    return monad_c_make_success(0);
}

struct monad_context_none
{
    struct monad_context_head head;
    monad_context_task task;
};

static struct monad_context_switcher_none
{
    struct monad_context_switcher_head head;
} context_switcher_none_instance = {
    {.contexts = 0,
     .self_destroy = monad_context_switcher_none_destroy,
     .create = monad_context_none_create,
     .destroy = monad_context_none_destroy,
     .suspend_and_call_resume = monad_context_none_suspend_and_call_resume,
     .resume = monad_context_none_resume,
     .resume_many = monad_context_none_resume_many}};

static thread_local size_t context_switcher_none_instance_within_resume_many;

monad_c_result
monad_context_switcher_none_create(monad_context_switcher *switcher)
{
    *switcher = &context_switcher_none_instance.head;
    return monad_c_make_success(0);
}

monad_context_switcher monad_context_switcher_none_instance()
{
    return &context_switcher_none_instance.head;
}

/*****************************************************************************/

static monad_c_result monad_context_none_create(
    monad_context *context, monad_context_switcher switcher_,
    monad_context_task task, const struct monad_context_task_attr *)
{
    struct monad_context_none *p = (struct monad_context_none *)calloc(
        1, sizeof(struct monad_context_none));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->task = task;
    *context = (monad_context)p;
    monad_context_reparent_switcher(*context, switcher_);
    return monad_c_make_success(0);
}

static monad_c_result monad_context_none_destroy(monad_context context)
{
    monad_context_reparent_switcher(context, nullptr);
    free(context);
    return monad_c_make_success(0);
}

static void
monad_context_none_suspend_and_call_resume(monad_context, monad_context)
{
    fprintf(
        stderr,
        "FATAL: The none context switcher cannot suspend tasks, and therefore "
        "cannot resume them.\n");
    abort();
}

static void monad_context_none_resume(monad_context, monad_context new_context)
{
    if (context_switcher_none_instance_within_resume_many == 0) {
        fprintf(
            stderr,
            "FATAL: The none context switcher cannot suspend tasks, and "
            "therefore cannot resume them.\n");
        abort();
    }
    struct monad_context_none *p = (struct monad_context_none *)new_context;
    // Execute the task
    p->head.is_running = true;
    p->task->result = p->task->user_code(p->task);
    p->head.is_running = false;
    p->task->detach(p->task);
}

static monad_c_result monad_context_none_resume_many(
    monad_context_switcher,
    monad_c_result (*resumed)(void *user_ptr, monad_context just_suspended),
    void *user_ptr)
{
    context_switcher_none_instance_within_resume_many++;
    monad_c_result r = resumed(user_ptr, nullptr);
    context_switcher_none_instance_within_resume_many--;
    return r;
}

/*****************************************************************************/

extern void monad_context_reparent_switcher(
    monad_context context, monad_context_switcher new_switcher)
{
    assert(context != nullptr);
    monad_context_switcher current_switcher =
        atomic_load_explicit(&context->switcher, memory_order_acquire);
    if (current_switcher == new_switcher) {
        return;
    }
    if (current_switcher != nullptr && new_switcher != nullptr &&
        current_switcher->create != new_switcher->create) {
        fprintf(
            stderr,
            "FATAL: If reparenting context switcher, the new parent "
            "must be the same type of context switcher.\n");
        abort();
    }
    if (!(current_switcher == monad_context_switcher_none_instance() &&
          new_switcher == monad_context_switcher_none_instance())) {
        if (current_switcher != nullptr) {
            atomic_fetch_sub_explicit(
                &current_switcher->contexts, 1, memory_order_relaxed);
        }
        atomic_store_explicit(
            &context->switcher, new_switcher, memory_order_release);
        if (new_switcher != nullptr) {
            atomic_fetch_add_explicit(
                &new_switcher->contexts, 1, memory_order_relaxed);
        }
        if (current_switcher == nullptr &&
            new_switcher != monad_context_switcher_none_instance()) {
            size_t const thread_db_slot =
                ~_thread_db_userspace_thread_allocate_thread_db_userspace_thread_index();
            memcpy(
                (size_t *)&context->thread_db_slot,
                &thread_db_slot,
                sizeof(size_t));
        }
        else if (
            current_switcher != monad_context_switcher_none_instance() &&
            new_switcher == nullptr) {
            deallocate_thread_db_userspace_thread_index(
                ~context->thread_db_slot);
        }
    }
}
