#include "context_switcher.h"

#include <monad/linked_list_impl_common.h>

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

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
#if MONAD_CONTEXT_TRACK_OWNERSHIP
    mtx_destroy(&p->contexts_list.lock);
#endif
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
#if MONAD_CONTEXT_TRACK_OWNERSHIP
    bool mutex_initialised;
#endif
} context_switcher_none_instance = {
    {.contexts = 0,
     .self_destroy = monad_context_switcher_none_destroy,
     .create = monad_context_none_create,
     .destroy = monad_context_none_destroy,
     .suspend_and_call_resume = monad_context_none_suspend_and_call_resume,
     .resume = monad_context_none_resume,
     .resume_many = monad_context_none_resume_many}
#if MONAD_CONTEXT_TRACK_OWNERSHIP
    ,
    .mutex_initialised = false
#endif
};

static thread_local size_t context_switcher_none_instance_within_resume_many;

monad_c_result
monad_context_switcher_none_create(monad_context_switcher *switcher)
{
    *switcher = &context_switcher_none_instance.head;
#if MONAD_CONTEXT_TRACK_OWNERSHIP
    if (!context_switcher_none_instance.mutex_initialised) {
        if (thrd_success !=
            mtx_init(
                &context_switcher_none_instance.head.contexts_list.lock,
                mtx_plain)) {
            abort();
        }
    }
#endif
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
#if MONAD_CONTEXT_TRACK_OWNERSHIP
        if (current_switcher != nullptr) {
            mtx_lock(&current_switcher->contexts_list.lock);
            LIST_REMOVE_ATOMIC_COUNTER(
                current_switcher->contexts_list,
                context,
                &current_switcher->contexts);
            mtx_unlock(&current_switcher->contexts_list.lock);
            assert(
                current_switcher ==
                atomic_load_explicit(&context->switcher, memory_order_acquire));
        }
        atomic_store_explicit(
            &context->switcher, new_switcher, memory_order_release);
        if (new_switcher != nullptr) {
            mtx_lock(&new_switcher->contexts_list.lock);
            LIST_APPEND_ATOMIC_COUNTER(
                new_switcher->contexts_list, context, &new_switcher->contexts);
            mtx_unlock(&new_switcher->contexts_list.lock);
            assert(
                new_switcher ==
                atomic_load_explicit(&context->switcher, memory_order_acquire));
        }
#else
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
#endif
    }
}
