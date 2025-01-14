#pragma once

#include "config.h"

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>

#ifndef MONAD_CONTEXT_CPP_DEFAULT_INITIALISE
    #ifdef __cplusplus
        #define MONAD_CONTEXT_CPP_DEFAULT_INITIALISE                           \
            {                                                                  \
            }
    #else
        #define MONAD_CONTEXT_CPP_DEFAULT_INITIALISE
    #endif
#endif

#ifdef __cplusplus
    #include <memory>
    #include <type_traits>

extern "C"
{
#endif

typedef struct monad_context_head *monad_context;

//! \brief How much memory to allocate to fit all implementations of `struct
//! monad_context_task_head`
#define MONAD_CONTEXT_TASK_ALLOCATION_SIZE (296)
//! \brief How many of those bytes are used by the i/o executor for its state
#define MONAD_ASYNC_TASK_FOOTPRINT (296)

//! \brief The public attributes of a task
typedef struct monad_context_task_head
{
    // These can be set by the user
    //! \brief The body of the task
    monad_c_result (*user_code)(struct monad_context_task_head *)
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;
    //! \brief Any user defined value
    void *user_ptr MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    //! \brief The context for the running task
    monad_context context MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    // The following are **NOT** user modifiable
    //! \brief Set to the result of the task on exit; also used as scratch
    //! during the task's suspend-resume cycles
    MONAD_CONTEXT_PUBLIC_CONST monad_c_result result
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

    //! \brief Set by the task implementation to a task detach implementation
    void (*MONAD_CONTEXT_PUBLIC_CONST detach)(
        struct monad_context_task_head *task)
        MONAD_CONTEXT_CPP_DEFAULT_INITIALISE;

#ifdef __cplusplus
    // Must not move in memory after construction
    monad_context_task_head &
    operator=(monad_context_task_head const &) = delete;
    monad_context_task_head &operator=(monad_context_task_head &&) = delete;
#endif
} *monad_context_task;
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_context_task_head) == 64);
    #ifdef __cplusplus
static_assert(alignof(struct monad_context_task_head) == 8);
    #endif
#endif
#ifdef __cplusplus
static_assert(std::is_aggregate_v<monad_context_task_head>);
#endif

//! \brief Attributes by which to construct a task
struct monad_context_task_attr
{
    //! \brief 0 chooses platform default stack size
    size_t stack_size;
};

typedef struct monad_context_switcher_head
{
    // These can be set by the user
    void *user_ptr;

    // The following are not user modifiable

    //! The number of contexts existing
    MONAD_CONTEXT_PUBLIC_CONST
    MONAD_CPP_STD atomic_uint contexts;

    //! \brief Destroys self
    monad_c_result (*const self_destroy)(
        struct monad_context_switcher_head *switcher);

    //! \brief Create a switchable context for a task
    monad_c_result (*const create)(
        monad_context *context, struct monad_context_switcher_head *switcher,
        monad_context_task task, struct monad_context_task_attr const *attr);
    //! \brief Destroys a switchable context
    monad_c_result (*const destroy)(monad_context context);

    /*! \brief If running within a switchable context, suspend it and call
    resume on the new context via its context switcher.

    Note that calling this from the main context will not work, as you will have
    no `current_context`. If in the main context, use `resume_many()` to
    get a suitable `current_context`.

    This call differs from `resume()` by being able to cope with `new_context`
    having a different context switcher to the current context. If the
    new context's switcher could be different from the current context's
    switcher, you must use this call.
    */
    void (*const suspend_and_call_resume)(
        monad_context current_context, monad_context new_context);

    /*! \brief Resume execution of a previously suspended switchable context.

    Generally this should only be called from within `resume_many()`'s
    `resumed()` callback, and not otherwise as you won't know if the new
    context's switcher is the same as the current context's.
    `suspend_and_call_resume()` does check if the switchers are identical and/or
    are of the same kind but different instances, and if so will take an
    optimised path.
    */
    void (*const resume)(
        monad_context current_context, monad_context new_context);
    /*! \brief To avoid having to set a resumption point per task when resuming
    many tasks from the central loop of the executor, set a single
    resumption point and call the supplied function every time a task
    resumed within the supplied function suspends. This can be very
    considerably more efficient for some types of context switcher.

    Generally you call `resume()` from within `resumed()` as the context
    switcher of the new context will be `switcher`.
    */
    monad_c_result (*const resume_many)(
        struct monad_context_switcher_head *switcher,
        monad_c_result (*resumed)(
            void *user_ptr, monad_context current_context_to_use_when_resuming),
        void *user_ptr);

    // Must come AFTER what the Rust bindings will use
} *monad_context_switcher;

typedef struct monad_context_switcher_impl
{
    //! \brief Create a switcher of contexts. The
    //! executor creates one of these per executor.
    monad_c_result (*const create)(monad_context_switcher *switcher);
} monad_context_switcher_impl;

typedef struct monad_context_head
{
    // The following are not user modifiable
    MONAD_CONTEXT_PUBLIC_CONST bool is_running, is_suspended;
    MONAD_CONTEXT_PUBLIC_CONST
    MONAD_CPP_ATOMIC(monad_context_switcher) switcher;

    // Must come AFTER what the Rust bindings will use
    size_t const thread_db_slot;

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
} *monad_context;

//! \brief For a context currently suspended, change which context switcher to
//! use for the next resumption. Context switchers must be of same type.
extern void monad_context_reparent_switcher(
    monad_context context, monad_context_switcher new_switcher);

//! \brief Destroys any context switcher
BOOST_OUTCOME_C_NODISCARD inline monad_c_result
monad_context_switcher_destroy(monad_context_switcher switcher)
{
    return switcher->self_destroy(switcher);
}

/*! \brief Creates a `setjmp`/`longjmp` based context switcher with each task
getting its own stack.

Note that an instance of this is NOT threadsafe, so you must either lock
a mutex around switching contexts using this context switcher or have a
context switcher instance per thread.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_context_switcher_sjlj_create(monad_context_switcher *switcher);
//! \brief Convenience struct for setting a `setjmp`/`longjmp` based context
//! switcher
extern monad_context_switcher_impl const monad_context_switcher_sjlj;

/*! \brief Creates a none context switcher which can't suspend-resume. Useful
for threadpool implementation.

As this context switcher never suspends and resumes, it is safe to use a single
instance of this across multiple threads. In fact, the current implementation
always returns a static instance, and destruction does nothing. You may
therefore find `monad_context_switcher_none_instance()` more useful.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_context_switcher_none_create(monad_context_switcher *switcher);
//! \brief Convenience struct for setting a none context
//! switcher
extern monad_context_switcher_impl const monad_context_switcher_none;
//! \brief Convenience obtainer of the static none context switcher.
extern monad_context_switcher monad_context_switcher_none_instance();

/*! \brief Creates a `fcontext` based context switcher with each task
getting its own stack. This is approx 2x faster than the `setjmp`/`longjmp`
context switcher if in a hot loop

Note that an instance of this is NOT threadsafe, so you must either lock
a mutex around switching contexts using this context switcher or have a
context switcher instance per thread.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_context_switcher_fcontext_create(monad_context_switcher *switcher);
//! \brief Convenience struct for setting a `fcontext` based context
//! switcher
extern monad_context_switcher_impl const monad_context_switcher_fcontext;

#ifdef __cplusplus
}

namespace monad
{
    namespace context
    {
        struct context_switcher_deleter
        {
            void operator()(monad_context_switcher t) const
            {
                to_result(monad_context_switcher_destroy(t)).value();
            }
        };

        using context_switcher_ptr = std::unique_ptr<
            monad_context_switcher_head, context_switcher_deleter>;

        //! \brief Construct a context switcher instance, and return it in a
        //! smart pointer
        inline context_switcher_ptr
        make_context_switcher(monad_context_switcher_impl impl)
        {
            monad_context_switcher ex;
            to_result(impl.create(&ex)).value();
            return context_switcher_ptr(ex);
        }

        struct context_deleter
        {
            monad_context_switcher switcher;

            void operator()(monad_context t) const
            {
                to_result(switcher->destroy(t)).value();
            }
        };

        using context_ptr =
            std::unique_ptr<monad_context_head, context_deleter>;

        //! \brief Construct a context instance, and return it in a
        //! smart pointer
        inline context_ptr make_context(
            monad_context_switcher impl, monad_context_task task,
            const struct monad_context_task_attr &attr)
        {
            monad_context ex;
            to_result(impl->create(&ex, impl, task, &attr)).value();
            return context_ptr(ex, {impl});
        }
    }
}
#endif

#ifndef MONAD_CONTEXT_DISABLE_INLINE_CUSTOM_GDB_THREAD_DB_LOAD
    #ifndef MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH
        #error                                                                 \
            "MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH should be defined to the directory of our custom libthread_db.so.1"
    #endif
    #define MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH_STRINGISE2(x) #x
    #define MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH_STRINGISE(x)               \
        MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH_STRINGISE2(x)
    #if defined(__ELF__)
        #ifdef __clang__
            #pragma clang diagnostic push
            #pragma clang diagnostic ignored "-Woverlength-strings"
        #endif
__asm__(
    ".pushsection \".debug_gdb_scripts\", \"MS\",@progbits,1\n"
    ".byte 4 /* Python Text */\n"
    ".ascii \"gdb.inlined-script.monad-context\\n\"\n"
    ".ascii \"import gdb\\n\"\n"
    ".ascii \"gdb.execute('set "
    "libthread-db-search-"
    "path " MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH_STRINGISE(
        MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH) "')\\n\"\n"

                                                 ".ascii \"print('NOTE: set "
                                                 "libthread-db-search-"
                                                 "path"
                                                 " " MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH_STRINGISE(
                                                     MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH) "')\\n\"\n"

                                                                                              ".byte 0\n"
                                                                                              ".popsection\n");
        #ifdef __clang__
            #pragma clang diagnostic pop
        #endif
    #endif
#endif
