/**
 * @file
 *
 * This file contains the implementation of the performance-sensitive
 * functions in the fiber library, which are all inlined and included in
 * fiber.h; see fiber-impl.md for the implementation notes
 */

#ifndef MONAD_FIBER_INTERNAL
    #error This is not a public interface, but included into fiber.h for performance reasons; users cannot include it
#endif

#include <errno.h>
#include <stdatomic.h>
#include <stdint.h>
#include <threads.h>

#include <monad/context/context_switcher.h>
#include <monad/core/assert.h>
#include <monad/core/likely.h>

#ifdef __cplusplus
extern "C"
{
#endif

extern int
_monad_run_queue_try_push_global(monad_run_queue_t *rq, monad_fiber_t *fiber);

struct monad_thread_executor_stats
{
    size_t total_run;
    size_t total_sleep;
    size_t total_immediate_wakeup;
};

/// Represents a thread (specifically the information about it needed to
/// execute a fiber)
struct monad_thread_executor
{
    monad_fiber_t *cur_fiber; ///< Fiber our thread is running (or null)
    monad_context_switcher switcher; ///< Thread's context switching machinery
    thrd_t thread; ///< Opaque system handle for the thread
    uint64_t thread_id; ///< System ID for thread, for debugging
    monad_fiber_suspend_info_t suspend_info; ///< To copy out suspension info
    struct monad_thread_executor_stats stats; ///< Stats for thread's executor
    SLIST_ENTRY(monad_thread_executor) next; ///< Linkage for all thread_locals
};

// This constinit is needed on macOS, where the TLS codegen strategy differs
// between C and C++. The thread executor TLS object lives in `fiber_thr.c`, so
// it follows the C language rules. These inline functions are usually also
// included in C++ translation units. Without constinit, this would emit
// references to an undefined C++ thread_local wrapper function on Darwin. See
// the comments in clang's `CodeGenModule::EmitGlobalVarDefinition` in
// CodeGenModule.cpp for more information
#ifdef __cplusplus
constinit
#endif
    extern thread_local struct monad_thread_executor _monad_tl_thr_exec;

static inline monad_thread_executor_t *_monad_current_thread_executor()
{
    extern void _monad_init_thread_executor(monad_thread_executor_t * thr_exec);
    if (MONAD_UNLIKELY(_monad_tl_thr_exec.thread == 0)) {
        _monad_init_thread_executor(&_monad_tl_thr_exec);
    }
    return &_monad_tl_thr_exec;
}

static inline monad_c_result
_monad_start_switch_to_fiber(void *arg0, monad_context thread_ctx)
{
    // Trampoline function needed by monad_context when we jump from a non-fiber
    // execution context (i.e., an ordinary thread) into a fiber context.
    monad_thread_executor_t *const thr_exec = (monad_thread_executor_t *)arg0;
    thr_exec->switcher->suspend_and_call_resume(
        thread_ctx, thr_exec->cur_fiber->switch_ctx);
    return monad_c_make_success(0);
}

static inline void _monad_finish_switch_to_fiber(monad_fiber_t *fiber)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&fiber->lock));
    fiber->state = MF_STATE_RUNNING;
    ++fiber->stats.total_run;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
}

static inline void _monad_suspend_fiber(
    monad_fiber_t *self, enum monad_fiber_state suspend_state,
    enum monad_fiber_suspend_type suspend_type, monad_c_result eval)
{
    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the context that originally jumped to us. That context is
    // typically running a lightweight scheduler, which decides which fiber to
    // run next and calls `monad_fiber_run`. Thus, we are always jumping back
    // into the body of `monad_fiber_run`, which will return and report our
    // suspension. `monad_fiber_run` disallows nested fiber execution, so we
    // know the previously executing context is the current thread's original
    // execution context
    monad_context_switcher switcher;
    monad_thread_executor_t *thr_exec;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&self->lock));
    switcher =
        atomic_load_explicit(&self->switch_ctx->switcher, memory_order_relaxed);
    thr_exec = (monad_thread_executor_t *)switcher->user_ptr;
    self->state = suspend_state;
    thr_exec->suspend_info.suspend_type = suspend_type;
    thr_exec->suspend_info.eval = eval;
    switcher->suspend_and_call_resume(self->switch_ctx, nullptr);

    // When suspend_and_call_resume returns, we have been resumed from the
    // suspension and are the current fiber again. Note that it is not safe to
    // touch the `thr_exec` variable anymore, as we are potentially resumed by
    // a different thread than we were suspended on, so it would now point at
    // the wrong thread object. If you need to access `thr_exec` here, it must
    // first be reseated by reading `self->switch_ctx->switcher->user_ptr`
    _monad_finish_switch_to_fiber(self);
}

/*
 * Implementation of the public API
 */

inline monad_fiber_t *monad_fiber_self()
{
    monad_thread_executor_t *const thr_exec = _monad_current_thread_executor();
    return thr_exec->cur_fiber;
}

inline int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info)
{
    int err;
    monad_c_result mcr;
    monad_thread_executor_t *thr_exec;

    MONAD_DEBUG_ASSERT(next_fiber != nullptr);
    thr_exec = _monad_current_thread_executor();
    if (MONAD_UNLIKELY(thr_exec->cur_fiber != nullptr)) {
        // The user tried to call monad_fiber_run from an active fiber; the
        // implementation explicitly disallows nested fibers
        return ENOTSUP;
    }

    // The fiber is usually already locked, since fibers remain locked when
    // returned from the run queue. However, you can also run a fiber directly
    // e.g., in the test suite. Acquire the lock if we don't have it
    if (MONAD_UNLIKELY(!monad_spinlock_is_self_owned(&next_fiber->lock))) {
        MONAD_SPINLOCK_LOCK(&next_fiber->lock);
    }

    if (next_fiber->state != MF_STATE_CAN_RUN) {
        // The user tried to resume a fiber that is not in a run state that
        // can be resumed
        switch (next_fiber->state) {
        case MF_STATE_INIT:
            [[fallthrough]];
        case MF_STATE_FINISHED:
            err = ENXIO;
            break;
        default:
            err = EBUSY;
            break;
        }
        MONAD_SPINLOCK_UNLOCK(&next_fiber->lock);
        return err;
    }

    if (atomic_load_explicit(
            &next_fiber->switch_ctx->switcher, memory_order_relaxed) !=
        thr_exec->switcher) {
        monad_context_reparent_switcher(
            next_fiber->switch_ctx, thr_exec->switcher);
        ++next_fiber->stats.total_migrate;
    }
    ++thr_exec->stats.total_run;
    thr_exec->cur_fiber = next_fiber;
    mcr = thr_exec->switcher->resume_many(
        thr_exec->switcher, _monad_start_switch_to_fiber, thr_exec);
    thr_exec->cur_fiber = nullptr;
    if (MONAD_FAILED(mcr)) {
        MONAD_SPINLOCK_UNLOCK(&next_fiber->lock);
        return (int)mcr.error.value; // XXX: just assuming this is errno domain?
    }
    if (MONAD_UNLIKELY(next_fiber->state == MF_STATE_CAN_RUN)) {
        // This fiber is ready to run again immediately despite the fact that
        // we just voluntarily switched away from it. This happens when it is a
        // fiber that has just yielded. If the yielding fiber also has a run
        // queue, we can just reschedule it immediately. We don't need (or want)
        // to unlock the fiber in that case, because the run queue expects it
        // to be locked
        MONAD_DEBUG_ASSERT(
            thr_exec->suspend_info.suspend_type == MF_SUSPEND_YIELD);
        if (MONAD_LIKELY(next_fiber->run_queue != nullptr)) {
            (void)_monad_run_queue_try_push_global(
                next_fiber->run_queue, next_fiber);
        }
        else {
            MONAD_SPINLOCK_UNLOCK(&next_fiber->lock);
        }
    }
    else {
        MONAD_SPINLOCK_UNLOCK(&next_fiber->lock);
    }
    if (suspend_info != nullptr) {
        memcpy(suspend_info, &thr_exec->suspend_info, sizeof *suspend_info);
    }
    return 0;
}

inline void monad_fiber_yield(monad_c_result eval)
{
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_DEBUG_ASSERT(self != nullptr);
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_suspend_fiber(self, MF_STATE_CAN_RUN, MF_SUSPEND_YIELD, eval);
}

static inline void _monad_fiber_sleep(
    monad_fiber_t *fiber, monad_fiber_prio_t wakeup_prio, void *wait_object)
{
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    if (MONAD_UNLIKELY(fiber->state == MF_STATE_WAKE_READY)) {
        // This is the sleep call half of a "skipped sleep"
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return;
    }
    if (wakeup_prio != MONAD_FIBER_PRIO_NO_CHANGE) {
        fiber->priority = wakeup_prio;
    }
    fiber->wait_object = wait_object;
    ++fiber->stats.total_sleep;
    _monad_suspend_fiber(
        fiber, MF_STATE_WAIT_QUEUE, MF_SUSPEND_SLEEP, (monad_c_result){});
}

static inline bool _monad_fiber_try_wakeup(monad_fiber_t *fiber)
{
    int rc;

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    if (MONAD_UNLIKELY(fiber->state != MF_STATE_WAIT_QUEUE)) {
        fiber->state = MF_STATE_WAKE_READY;
        ++fiber->stats.total_skipped_sleeps;
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return true;
    }
    if (MONAD_UNLIKELY(fiber->run_queue == nullptr)) {
        // XXX: only for the test suite?
        fiber->state = MF_STATE_CAN_RUN;
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return true;
    }
    rc = _monad_run_queue_try_push_global(fiber->run_queue, fiber);
    if (MONAD_LIKELY(rc == 0)) {
        return true;
    }
    // We are only permitted to report failure if trying again might succeed,
    // because our caller must repeatedly try again until this succeeds.
    // The run queue reports ENOBUFS when the queue is full. Presumably
    // something else must be draining it. If not, this will manifest as an
    // infinite loop with `total_sched_fail` monotonically increasing.
    MONAD_ASSERT(rc == ENOBUFS);
    fiber->state = MF_STATE_WAIT_QUEUE;
    ++fiber->stats.total_sched_fail;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return false;
}

#ifdef __cplusplus
} // extern "C"
#endif
