#pragma once

#ifdef __cplusplus
#define MONAD_NODISCARD [[nodiscard]]
#define MONAD_STD std::
#define MONAD_ATOMIC(X) std::atomic<X>
#else
#define MONAD_NODISCARD __attribute__((warn_unused_result))
#define MONAD_STD
#define MONAD_ATOMIC(X) _Atomic X
#endif

#ifndef MONAD_PCONST
    #ifdef MONAD_SOURCE
        #define MONAD_PCONST
    #else
        #define MONAD_PCONST const
    #endif
#endif

#include "config.h"

#include <sys/queue.h>

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

struct monad_async_context;
struct monad_async_context_switcher;
struct monad_async_task;
struct monad_async_task_attr;

/// The address sanitizer can analyze stack frames, so it must be told about
/// our fiber's stack
struct monad_async_asan_info {
    union
    {
        void *fake_stack_save;
        unsigned valgrind_stack_id;
    };

    void const *bottom;
    size_t size;
};

/// Defines the switcher interface
///
/// Multiple user-space context switcher backends are available
/// (setjmp/longjmp-based, Boost.Context-based, C++20 coroutine-based, etc.).
/// Each implementation provides a table of function pointers to implement
/// the interface.
struct monad_async_context_switcher_ops {
    /// Create a switchable context for a task
    monad_async_result (*create_context)(
        struct monad_async_context **context,
        struct monad_async_context_switcher *switcher,
        struct monad_async_task *task,
        const struct monad_async_task_attr *attr);

    /// Destroys a switchable context created by create_context
    monad_async_result (*destroy_context)(struct monad_async_context *context);

    /// Suspend the currently running switchable context and resume on the
    /// new context
    void (*suspend_and_call_resume)(
        struct monad_async_context *current_context,
        struct monad_async_context *new_context);

    /// Resume execution of a previously suspended switchable context.
    /// Some context switchers will return from this function when the resumed
    /// task next suspends, others will resume at the suspension point set by
    /// `resume_many`.
    void (*const resume)(
        struct monad_async_context *current_context,
        struct monad_async_context *new_context);

    /// Set a single resumption point which calls the supplied function every
    /// time a task resumed within the supplied function suspends.
    monad_async_result (*resume_many)(
        struct monad_async_context_switcher *switcher,
        monad_async_result (*resumed)(
            void *user_ptr,
            struct monad_async_context *current_context_to_use_when_resuming),
        void *user_ptr);

    /// Destroys the switcher object; the factory that creates the switcher
    /// hangs its cleanup routine here
    monad_async_result (*destroy_self)(
        struct monad_async_context_switcher *switcher);
};

/// Object which manages the low-level details of switching between two
/// user-space contexts
struct monad_async_context_switcher
{
    void *user_ptr; ///< Opaque user data, passed into the resume_many callback

    /*
     * The following fields are not user modifiable
     */

    MONAD_PCONST MONAD_STD atomic_uint contexts; ///< Number of contexts
    const struct monad_async_context_switcher_ops
        *switcher_ops; ///< Switcher backend we're using

    // Must come AFTER what the Rust bindings will use
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    struct
    {
        mtx_t lock;                                ///< Protects contexts list
        LIST_HEAD(, monad_async_context) contexts; ///< All contexts using switcher
        size_t count;                              ///< Size of contexts list
    } context_tracker;
#endif
};

typedef struct monad_async_context_switcher_factory
{
    /// Create a switcher of contexts; this is called by the executor; the
    /// corresponding destroy routine is part of the operations structure,
    /// (see destroy_self)
    monad_async_result (*const create)(struct monad_async_context_switcher **switcher);
} monad_async_context_switcher_factory;

enum monad_async_run_state {
    Running,
    Suspended
};

struct monad_async_context
{
    enum monad_async_run_state state;
    MONAD_ATOMIC(struct monad_async_context_switcher*) switcher;

    // Must come AFTER what the Rust bindings will use
#if MONAD_ASYNC_CONTEXT_TRACK_OWNERSHIP
    void *stack_bottom, *stack_current, *stack_top;
    LIST_ENTRY(monad_aync_context) linkage; ///< For switcher's "all contexts" list
#endif

    struct monad_async_asan_info asan_stack_info;
};

extern void monad_async_context_reparent_switcher(
    struct monad_async_context *context,
    struct monad_async_context_switcher *new_switcher);

/// Destroys any context switcher
MONAD_NODISCARD inline monad_async_result
monad_async_context_switcher_destroy(struct monad_async_context_switcher* s)
{
    return s->switcher_ops->destroy_self(s);
}

/// Creates a `setjmp`/`longjmp` based context switcher with each task getting
/// its own stack
MONAD_NODISCARD extern monad_async_result
monad_async_context_switcher_create_sjlj(
    struct monad_async_context_switcher **switcher);

/// Convenience struct for setting a `setjmp`/`longjmp` based context
/// switcher
extern monad_async_context_switcher_factory const
    monad_async_context_switcher_sjlj_factory;

/**
 * Creates a none context switcher which can't suspend-resume. Useful
 * for threadpool implementation.
 *
 * As this context switcher never suspends and resumes, it is safe to use a
 * single instance of this across multiple threads. In fact, the current
 * implementation always returns a static instance, and destruction does
 * nothing. You may therefore find
 * `monad_async_context_switcher_none_instance()` more useful.
 */
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_context_switcher_create_none(
    struct monad_async_context_switcher **switcher);

/// Convenience struct for setting a none context switcher
extern monad_async_context_switcher_factory const
    monad_async_context_switcher_none_factory;

/// Convenience obtainer of the static none context switcher.
extern struct monad_async_context_switcher*
monad_async_context_switcher_get_none_instance();

/// Creates a Monad Fiber context switcher
MONAD_NODISCARD extern monad_async_result
monad_async_context_switcher_create_fiber(
    struct monad_async_context_switcher **switcher);

//! \brief Convenience struct for setting a Monad Fiber context switcher
extern monad_async_context_switcher_factory const
    monad_async_context_switcher_fiber_factory;

#ifdef __cplusplus
}
#endif
