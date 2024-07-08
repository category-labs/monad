#pragma once

#include "config.h"

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>

#ifndef MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    #ifdef NDEBUG
        #define MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP 0
    #else
        #define MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP 1
    #endif
#endif

#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    #include <threads.h>
#endif

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_async_task_head *monad_async_task;

struct monad_async_task_attr;

typedef struct monad_async_context_head *monad_async_context;

typedef struct monad_async_context_switcher_head
{
    // These can be set by the user
    void *user_ptr;

    // The following are not user modifiable

    //! The number of contexts existing
    MONAD_ASYNC_PUBLIC_CONST
    MONAD_ASYNC_CPP_STD atomic_uint contexts;

    //! \brief Destroys self
    monad_async_result (*const self_destroy)(
        struct monad_async_context_switcher_head *switcher);

    //! \brief Create a switchable context for a task
    monad_async_result (*const create)(
        monad_async_context *context,
        struct monad_async_context_switcher_head *switcher,
        monad_async_task task, const struct monad_async_task_attr *attr);
    //! \brief Destroys a switchable context
    monad_async_result (*const destroy)(monad_async_context context);
    //! \brief If running within a switchable context, suspend it and call
    //! resume on the new context via its context switcher. This allows for
    //! `new_context` to use a different type of context switcher to this one.
    void (*const suspend_and_call_resume)(
        monad_async_context current_context, monad_async_context new_context);
    //! \brief Resume execution of a previously suspended switchable context.
    //! Some context switchers will return from this function when the resumed
    //! task next suspends, others will resume at the suspension point set by
    //! `resume_many`. `new_context` must have the same context switcher as
    //! `current_context`.
    void (*const resume)(
        monad_async_context current_context, monad_async_context new_context);
    //! \brief To avoid having to set a resumption point per task when resuming
    //! many tasks from the central loop of the executor, set a single
    //! resumption point and call the supplied function every time a task
    //! resumed within the supplied function suspends. This can be very
    //! considerably more efficient for some types of context switcher.
    monad_async_result (*const resume_many)(
        struct monad_async_context_switcher_head *switcher,
        monad_async_result (*resumed)(
            void *user_ptr,
            monad_async_context current_context_to_use_when_resuming),
        void *user_ptr);

    // Must come AFTER what the Rust bindings will use
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    struct
    {
        mtx_t lock;
        monad_async_context front, back;
        size_t count;
    } contexts_list;
#endif
} *monad_async_context_switcher;

typedef struct monad_async_context_switcher_impl
{
    //! \brief Create a switcher of contexts. The
    //! executor creates one of these per executor.
    monad_async_result (*const create)(monad_async_context_switcher *switcher);
} monad_async_context_switcher_impl;

typedef struct monad_async_context_head
{
    // The following are not user modifiable
    bool is_running, is_suspended;
    MONAD_ASYNC_ATOMIC(monad_async_context_switcher) switcher;

    // Must come AFTER what the Rust bindings will use
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    void *stack_bottom, *stack_current, *stack_top;
    monad_async_context prev, next;
#endif

    struct
    {
        union
        {
            void *fake_stack_save;
            unsigned valgrind_stack_id;
            void *fiber;
        };

        void const *bottom;
        size_t size;
    } sanitizer;
} *monad_async_context;

extern void monad_async_context_reparent_switcher(
    monad_async_context context, monad_async_context_switcher new_switcher);

//! \brief Destroys any context switcher
BOOST_OUTCOME_C_NODISCARD inline monad_async_result
monad_async_context_switcher_destroy(monad_async_context_switcher switcher)
{
    return switcher->self_destroy(switcher);
}

//! \brief Creates a `setjmp`/`longjmp` based context switcher with each task
//! getting its own stack
BOOST_OUTCOME_C_NODISCARD extern monad_async_result
monad_async_context_switcher_sjlj_create(
    monad_async_context_switcher *switcher);
//! \brief Convenience struct for setting a `setjmp`/`longjmp` based context
//! switcher
extern monad_async_context_switcher_impl const
    monad_async_context_switcher_sjlj;

/*! \brief Creates a none context switcher which can't suspend-resume. Useful
for threadpool implementation.

As this context switcher never suspends and resumes, it is safe to use a single
instance of this across multiple threads. In fact, the current implementation
always returns a static instance, and destruction does nothing. You may
therefore find `monad_async_context_switcher_none_instance()` more useful.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_async_result
monad_async_context_switcher_none_create(
    monad_async_context_switcher *switcher);
//! \brief Convenience struct for setting a none context
//! switcher
extern monad_async_context_switcher_impl const
    monad_async_context_switcher_none;
//! \brief Convenience obtainer of the static none context switcher.
extern monad_async_context_switcher
monad_async_context_switcher_none_instance();

//! \brief Creates a `fcontext` based context switcher with each task
//! getting its own stack. This is approx 2x faster than the `setjmp`/`longjmp`
//! context switcher if in a hot loop
BOOST_OUTCOME_C_NODISCARD extern monad_async_result
monad_async_context_switcher_fcontext_create(
    monad_async_context_switcher *switcher);
//! \brief Convenience struct for setting a `fcontext` based context
//! switcher
extern monad_async_context_switcher_impl const
    monad_async_context_switcher_fcontext;

#ifdef __cplusplus
}
#endif
