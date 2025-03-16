#pragma once

/**
 * @file
 *
 * This file defines the interface for our lightweight fiber library
 */

#include <stddef.h>
#include <stdint.h>
#include <sys/queue.h>

#include <monad/context/context_switcher.h>
#include <monad/core/c_result.h>
#include <monad/core/spinlock.h>
#include <monad/mem/cma/cma_alloc.h>

#ifdef __cplusplus
extern "C"
{
#endif

/*
 * Forward declaration of opaque / incomplete types defined in other headers
 */

typedef void *monad_fcontext_t;
typedef struct monad_run_queue monad_run_queue_t;
typedef struct monad_thread_executor monad_thread_executor_t;

/*
 * Types defined by fiber.h
 */

typedef struct monad_fiber monad_fiber_t;
typedef struct monad_fiber_args monad_fiber_args_t;
typedef struct monad_fiber_attr monad_fiber_attr_t;
typedef struct monad_fiber_suspend_info monad_fiber_suspend_info_t;

typedef monad_c_result(monad_fiber_ffunc_t)(monad_fiber_args_t);
typedef TAILQ_HEAD(monad_fiber_wait_queue, monad_fiber)
    monad_fiber_wait_queue_t;
typedef int64_t monad_fiber_prio_t;

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
static monad_fiber_prio_t const MONAD_FIBER_PRIO_HIGHEST = INT64_MIN;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_LOWEST = INT64_MAX - 1;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_NO_CHANGE = INT64_MAX;

#define MONAD_FIBER_MAX_ARGS (4)

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
/// Various objects (fibers, wait channels, etc.) can be given a name for the
/// sake of debugging; the strlen(3) of the name cannot exceed this value
#define MONAD_FIBER_NAME_LEN (31)

enum monad_fiber_suspend_type : unsigned
{
    MF_SUSPEND_NONE,
    MF_SUSPEND_YIELD,
    MF_SUSPEND_SLEEP,
    MF_SUSPEND_RETURN
};

/// When a fiber is suspended, monad_fiber_run will fill out one of these
/// structures to describe the reason for the suspension
struct monad_fiber_suspend_info
{
    enum monad_fiber_suspend_type suspend_type; ///< Reason for last suspension
    monad_c_result eval; ///< Value (for YIELD / RETURN)
};

/// Opaque arguments are passed into fiber functions using this structure
struct monad_fiber_args
{
    uintptr_t arg[MONAD_FIBER_MAX_ARGS];
};

/// Creation attributes for monad_fiber_create
struct monad_fiber_attr
{
    size_t stack_size; ///< Size of fiber stack
    monad_allocator_t *alloc; ///< Allocator used for the monad_fiber_t object
};

/*
 * Public interface: functions that are called by users of the library
 */

/// Create a fiber, given a description of its attributes (if nullptr is passed,
/// the default attributes will be used)
int monad_fiber_create(
    monad_fiber_attr_t const *create_attr, monad_fiber_t **fiber);

/// Destroy a fiber previously created with monad_fiber_create
void monad_fiber_destroy(monad_fiber_t *fiber);

/// Set the function that the fiber will run; this may be called multiple times,
/// to reuse the fiber's resources (e.g., its stack) to run new functions
int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, monad_fiber_args_t fargs);

/// Returns the structure representing the currently executing fiber; returns
/// nullptr if the current execution context is not a fiber, i.e., if it is an
/// ordinary thread
static monad_fiber_t *monad_fiber_self();

/// Begin running a fiber's function on the calling thread, or resume that
/// function at the suspension point, if it was suspended; this call returns the
/// next time the function suspends, and populates @ref suspend_info with info
/// about that suspension
static int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info);

/// Similar to sched_yield(2) or pthread_yield_np(3), but for fibers: yields
/// from the currently-running fiber back to the previously-running fiber
static void monad_fiber_yield(monad_c_result eval);

/// Get the name of a fiber, for debugging and instrumentation
int monad_fiber_get_name(monad_fiber_t *fiber, char *name, size_t size);

/// Set the name of a fiber, for debugging and instrumentation
int monad_fiber_set_name(monad_fiber_t *fiber, char const *name);

/// Returns true if the given fiber would execute immediately if monad_fiber_run
/// is called; be aware that this has a TOCTOU race in multithreaded code,
/// e.g., this could change asynchronously because of another thread
static bool monad_fiber_is_runnable(monad_fiber_t const *fiber);

/// Set the context switcher implementation used by the calling thread; returns
/// the previously active switcher implementation for this thread; this must be
/// called prior to the first call to monad_fiber_run or
/// monad_fiber_set_function by this thread, otherwise it will have no effect
monad_context_switcher_impl const *
monad_fiber_set_context_switcher_impl(monad_context_switcher_impl const *);

/// The global default context switcher implementation to use, if no
/// implementation is set via a call to monad_fiber_set_context_switcher_impl
extern monad_context_switcher_impl const
    *g_monad_fiber_default_context_switcher_impl;

// clang-format off

struct monad_fiber_stats
{
    size_t total_reset;      ///< # of times monad_fiber_set_function is called
    size_t total_run;        ///< # of times fiber has been run (1 + <#resumed>)
    size_t total_sleep;      ///< # of times exec slept on a sync. primitive
    size_t total_sched_fail; ///< # times scheduling immediately failed
    size_t total_spurious_wakeups; ///< # times woken up just to sleep again
    size_t total_skipped_sleeps;   ///< # times signaled before needing sleep
    size_t total_migrate;          ///< # of times moved between threads
};

/*
 * Fiber structures and inline functions
 */

enum monad_fiber_state : unsigned;

/// Object which represents a user-created fiber; users can set the priority
/// field of the current fiber(e.g., ` monad_fiber_self()->priority += 100` )
/// but should not directly write to other fields
struct monad_fiber
{
    struct monad_context_task_head task; ///< monad_context runnable object
    monad_context switch_ctx;            ///< monad_context state object
    alignas(64) monad_spinlock_t lock;   ///< Protects most fiber fields
    enum monad_fiber_state state;        ///< Run state fiber is in
    unsigned fiber_id;                   ///< Unique ID of fiber
    monad_fiber_prio_t priority;         ///< Scheduling priority
    TAILQ_ENTRY(monad_fiber) wait_link;  ///< Linkage for wait_queue
#if MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO
    __int128_t rq_priority;              ///< Adjusted priority, see run_queue.h
#endif
    monad_run_queue_t *run_queue;        ///< Most recent run queue
    void *wait_object;                   ///< Synch. primitive we're sleeping on
    void *user_data;                     ///< Opaque user data
    struct monad_fiber_stats stats;      ///< Statistics about this context
    monad_fiber_ffunc_t *ffunc;          ///< Fiber function to run
    monad_fiber_args_t fargs;            ///< Opaque arguments passed to ffunc
    monad_fiber_attr_t create_attr;      ///< Attributes we were created with
    monad_memblk_t self_memblk;          ///< Dynamic memory block we live in
    char name[MONAD_FIBER_NAME_LEN + 1]; ///< Context name, for debugging
};

enum monad_fiber_state : unsigned
{
    MF_STATE_INIT,       ///< Fiber function not run yet
    MF_STATE_CAN_RUN,    ///< Not running but able to run
    MF_STATE_WAIT_QUEUE, ///< Asleep on a wait queue
    MF_STATE_WAKE_READY, ///< Ready to wake up on a condition immediately
    MF_STATE_RUN_QUEUE,  ///< Scheduled on a run queue
    MF_STATE_RUNNING,    ///< Fiber or thread is running
    MF_STATE_FINISHED    ///< Suspended by function return; fiber is finished
};

// clang-format on

inline bool monad_fiber_is_runnable(monad_fiber_t const *fiber)
{
    MONAD_DEBUG_ASSERT(fiber != nullptr);
    return __atomic_load_n(&fiber->state, __ATOMIC_SEQ_CST) == MF_STATE_CAN_RUN;
}

#if __cplusplus
} // extern "C"
#endif

#define MONAD_FIBER_INTERNAL
#include "fiber_inline.h"
#undef MONAD_FIBER_INTERNAL
