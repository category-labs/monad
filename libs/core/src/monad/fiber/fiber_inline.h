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
#include <stdint.h>
#include <threads.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>

#include <monad-boost/context/fcontext.h>

#if MONAD_HAS_ASAN
    #include <sanitizer/asan_interface.h>
#endif

#ifdef __cplusplus
extern "C"
{
#endif

extern int
_monad_run_queue_try_push_global(monad_run_queue_t *rq, monad_fiber_t *fiber);

/// Represents a thread (specifically the information about it needed to
/// execute a fiber)
struct monad_thread_executor
{
    monad_fcontext_t md_suspended_ctx; ///< Saved thread's ctx when suspended
    monad_fiber_t *cur_fiber; ///< Fiber this thread is running (or nullptr)
    thrd_t thread; ///< Opaque system handle for the thread
    uint64_t thread_id; ///< Public ID for the thread, for debugging
    struct monad_fiber_stack stack; ///< Descriptor for thread stack
    monad_fiber_suspend_info_t suspend_info; ///< To copy out suspension info
    SLIST_ENTRY(monad_thread_executor) next; ///< Linkage for all thread_locals
#if MONAD_HAS_ASAN
    void *fake_stack_save; ///< For ASAN stack support
#endif
};

#if MONAD_HAS_ASAN
    #define MONAD_FIBER_ASAN_START_SWITCH(FAKE_STACK_SAVE, STACK_DESC)         \
        __sanitizer_start_switch_fiber(                                        \
            (FAKE_STACK_SAVE),                                                 \
            (STACK_DESC).stack_bottom,                                         \
            (size_t)((uint8_t *)((STACK_DESC).stack_top) -                     \
                     (uint8_t *)((STACK_DESC).stack_bottom)))

    #define MONAD_FIBER_ASAN_FINISH_SWITCH(FAKE_STACK_SAVE)                    \
        __sanitizer_finish_switch_fiber((FAKE_STACK_SAVE), nullptr, nullptr);
#else
    #define MONAD_FIBER_ASAN_START_SWITCH(...)
    #define MONAD_FIBER_ASAN_FINISH_SWITCH(...)
#endif

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

// When a fiber stack is first used or is resumed after having been suspended,
// this function must be called to finish the context switch.
//
// There are two places in the code where this can occur:
//
//   1. When a fiber initially begins running. This means at the beginning of
//      the fiber's entrypoint function (the function specified in the
//      monad_make_fcontext call)
//
//   2. Immediately after a call to monad_jump_fcontext returns, in the
//      `_monad_suspend_fiber` function. Note that a return from
//      monad_jump_fcontext implies we have been resumed from the suspension
//      implied by the jump, thus the switch we are finishing is not the same
//      one that was started by the start switch call
//
// We are given a `struct monad_transfer_t`, with two members:
//
//   data - the `struct monad_thread_executor_t *` for the thread that
//          invoked the `monad_fiber_run` call that returned control back to us
//   fctx - the context pointer (effectively the suspension point) within
//          the thread where it was suspended upon the switch back to us
//          (i.e., pointing inside the stack frame of monad_fiber_run)
static inline void
_monad_finish_switch_to_fiber(struct monad_transfer_t xfer_from)
{
    monad_thread_executor_t *const thr_exec =
        (monad_thread_executor_t *)xfer_from.data;
    monad_fiber_t *const fiber = thr_exec->cur_fiber;

    MONAD_FIBER_ASAN_FINISH_SWITCH(fiber->fake_stack_save);
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&fiber->lock));

    // Remember where the thread context suspended
    thr_exec->md_suspended_ctx = xfer_from.fctx;

    // Finish book-keeping to become the new running fiber
    fiber->state = MF_STATE_RUNNING;
    if (MONAD_UNLIKELY(fiber->thr_exec != thr_exec)) {
        fiber->thr_exec = thr_exec;
        ++fiber->stats.total_migrate;
    }
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
    monad_thread_executor_t *const thr_exec = self->thr_exec;
    thr_exec->suspend_info.suspend_type = suspend_type;
    thr_exec->suspend_info.eval = eval;
    self->state = suspend_state;
    // TODO(ken): we never pass nullptr here to cleanup the fake stack save,
    //   because the stack can be reused even if the function is done; likely
    //   we'll never fix this because it will be replaced with Niall's stuff
    //   anyway.
    MONAD_FIBER_ASAN_START_SWITCH(&self->fake_stack_save, thr_exec->stack);
    struct monad_transfer_t const resume_xfer =
        monad_jump_fcontext(thr_exec->md_suspended_ctx, thr_exec);
    _monad_finish_switch_to_fiber(resume_xfer);
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
    struct monad_transfer_t resume_xfer;
    monad_thread_executor_t *thr_exec;
    // For ASAN:
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack;

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

    thr_exec->cur_fiber = next_fiber;
    MONAD_FIBER_ASAN_START_SWITCH(
        &thr_exec->fake_stack_save, next_fiber->stack);
    // Call the machine-dependent context switch function, monad_jump_fcontext.
    // This atomically suspends the thread's execution context and begins
    // executing the fiber's context at its last suspension point. When we are
    // resumed at some later time, it will appear as through we've returned
    // from this function call to `monad_jump_fcontext`, and we will again be
    // the currently running context.
    resume_xfer = monad_jump_fcontext(next_fiber->md_suspended_ctx, thr_exec);
    MONAD_FIBER_ASAN_FINISH_SWITCH(thr_exec->fake_stack_save);
    next_fiber->md_suspended_ctx = resume_xfer.fctx;
    if (suspend_info != nullptr) {
        memcpy(suspend_info, &thr_exec->suspend_info, sizeof *suspend_info);
    }

    if (MONAD_UNLIKELY(next_fiber->state == MF_STATE_CAN_RUN)) {
        // The fiber is ready to run again immediately despite the fact that we
        // just voluntarily switched away from it. This should happen if it is
        // a fiber that has just yielded. If the yielding fiber also has a run
        // queue, we can just reschedule it immediately. We don't need (or
        // want) to unlock the fiber in that case, because the run queue
        // expects it to be locked
        MONAD_DEBUG_ASSERT(
            next_fiber != nullptr &&
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
    thr_exec->cur_fiber = nullptr;
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
