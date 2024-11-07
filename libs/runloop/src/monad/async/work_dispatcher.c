#include "monad/async/work_dispatcher.h"

#include "executor_impl.h"

#include <errno.h>
#include <stdlib.h>
#include <threads.h>

struct monad_async_work_dispatcher_executor_impl
{
    struct monad_async_work_dispatcher_executor_head head;
    struct monad_async_executor_impl derived;
    struct monad_async_work_dispatcher_executor_impl *prev, *next;
    atomic_bool please_quit;
    struct timespec last_work_executed;
};

LIST_DECLARE_N(struct monad_async_work_dispatcher_executor_impl);

struct monad_async_work_dispatcher_impl
{
    struct monad_async_work_dispatcher_head head;
    uint32_t spin_before_sleep_ms;

    // all items below this require taking the lock
    mtx_t lock;
    int workloads_changed_waiting;
    cnd_t workloads_changed;

    struct
    {
        LIST_DEFINE_N(
            working, struct monad_async_work_dispatcher_executor_impl);
        LIST_DEFINE_N(idle, struct monad_async_work_dispatcher_executor_impl);
    } executors;

    LIST_DEFINE_P(tasks_awaiting_dispatch, struct monad_async_task_impl);
};

monad_c_result monad_async_work_dispatcher_create(
    monad_async_work_dispatcher *dp,
    struct monad_async_work_dispatcher_attr *attr)
{
    struct monad_async_work_dispatcher_impl *p =
        (struct monad_async_work_dispatcher_impl *)calloc(
            1, sizeof(struct monad_async_work_dispatcher_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->spin_before_sleep_ms = attr->spin_before_sleep_ms;
    if (thrd_success != mtx_init(&p->lock, mtx_plain)) {
        (void)monad_async_work_dispatcher_destroy(
            (monad_async_work_dispatcher)p);
        return monad_c_make_failure(errno);
    }
    if (thrd_success != cnd_init(&p->workloads_changed)) {
        (void)monad_async_work_dispatcher_destroy(
            (monad_async_work_dispatcher)p);
        return monad_c_make_failure(errno);
    }
    *dp = (monad_async_work_dispatcher)p;
    return monad_c_make_success(0);
}

monad_c_result
monad_async_work_dispatcher_destroy(monad_async_work_dispatcher dp)
{
    struct monad_async_work_dispatcher_impl *p =
        (struct monad_async_work_dispatcher_impl *)dp;
    cnd_destroy(&p->workloads_changed);
    mtx_destroy(&p->lock);
    free(p);
    return monad_c_make_success(0);
}

monad_c_result monad_async_work_dispatcher_executor_create(
    monad_async_work_dispatcher_executor *ex, monad_async_work_dispatcher dp_,
    struct monad_async_work_dispatcher_executor_attr *attr)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)calloc(
            1, sizeof(struct monad_async_work_dispatcher_executor_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
        (void)monad_async_work_dispatcher_executor_destroy(
            (monad_async_work_dispatcher_executor)p),
        monad_async_executor_create_impl(&p->derived, &attr->derived));
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)dp_;
    struct monad_async_work_dispatcher_executor_head head = {
        .derived = &p->derived.head,
        .dispatcher = dp_,
        .is_idle = true,
        .is_working = false};
    memcpy(&p->head, &head, sizeof(head));
    if (thrd_success != mutex_lock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    LIST_APPEND_ATOMIC_COUNTER(dp->executors.idle, p, &dp_->executors.idle);
    if (thrd_success != mutex_unlock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    *ex = (monad_async_work_dispatcher_executor)p;
    return monad_c_make_success(0);
}

monad_c_result monad_async_work_dispatcher_executor_destroy(
    monad_async_work_dispatcher_executor ex)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
        monad_async_executor_destroy_impl(&p->derived));
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)p->head.dispatcher;
    if (thrd_success != mutex_lock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    if (atomic_load_explicit(&p->head.is_idle, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            dp->executors.idle, p, &dp->head.executors.idle);
    }
    if (atomic_load_explicit(&p->head.is_working, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            dp->executors.working, p, &dp->head.executors.working);
    }
    if (thrd_success != mutex_unlock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    free(p);
    return monad_c_make_success(0);
}

monad_c_result monad_async_work_dispatcher_executor_run(
    monad_async_work_dispatcher_executor ex)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    if (atomic_load_explicit(&p->please_quit, memory_order_acquire) &&
        atomic_load_explicit(
            &p->derived.head.tasks_pending_launch, memory_order_acquire) == 0 &&
        atomic_load_explicit(
            &p->derived.head.tasks_running, memory_order_acquire) == 0 &&
        atomic_load_explicit(
            &p->derived.head.tasks_suspended, memory_order_acquire) == 0) {
        return monad_c_make_success(-1);
    }
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)p->head.dispatcher;
    struct timespec ts = {0, 0}, now;
    clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
    int64_t const ns_since_last_work_executed =
        timespec_diff(&now, &p->last_work_executed);
    if (ns_since_last_work_executed / 1000000 > dp->spin_before_sleep_ms) {
        ts.tv_sec = 30;
    }
retry:
    monad_c_result r = monad_async_executor_run(&p->derived.head, 256, &ts);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        if (outcome_status_code_equal_generic(&r.error, ETIME) ||
            outcome_status_code_equal_generic(&r.error, ECANCELED)) {
            r.value = 0;
        }
        else {
            BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(r);
        }
    }
    if (r.value > 0) {
        clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
        p->last_work_executed = now;
        return r;
    }
    // No work was executed last run, see if there is more work for me to launch
    if (!atomic_load_explicit(&p->please_quit, memory_order_acquire) &&
        atomic_load_explicit(
            &dp->head.tasks_awaiting_dispatch, memory_order_relaxed) > 0) {
        if (thrd_success != mutex_lock(&dp->lock)) {
            return monad_c_make_failure(errno);
        }
        for (monad_async_priority n = monad_async_priority_high;
             n < monad_async_priority_max;
             n++) {
            if (dp->tasks_awaiting_dispatch[n].count > 0) {
                struct monad_async_task_impl *item =
                    dp->tasks_awaiting_dispatch[n].front;
                // item->head.is_awaiting_dispatch is set to false by attach op
                LIST_REMOVE_ATOMIC_COUNTER(
                    dp->tasks_awaiting_dispatch[n],
                    item,
                    &dp->head.tasks_awaiting_dispatch);
                r = monad_async_task_attach(
                    &p->derived.head, &item->head, nullptr);
                // Failure here is likely a logic error
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(r);
                if (dp->workloads_changed_waiting > 0) {
#if MONAD_HAVE_TSAN
                    __tsan_mutex_pre_signal(&dp->lock, 0);
#endif
                    cnd_broadcast(&dp->workloads_changed);
#if MONAD_HAVE_TSAN
                    __tsan_mutex_post_signal(&dp->lock, 0);
#endif
                }
                if (thrd_success != mutex_unlock(&dp->lock)) {
                    return monad_c_make_failure(errno);
                }
                goto retry;
            }
        }
        if (thrd_success != mutex_unlock(&dp->lock)) {
            return monad_c_make_failure(errno);
        }
    }
    else if (
        atomic_load_explicit(
            &p->derived.head.tasks_pending_launch, memory_order_acquire) == 0 &&
        atomic_load_explicit(
            &p->derived.head.tasks_running, memory_order_acquire) == 0 &&
        atomic_load_explicit(
            &p->derived.head.tasks_suspended, memory_order_acquire) == 0) {
        // We have become idle
        if (thrd_success != mutex_lock(&dp->lock)) {
            return monad_c_make_failure(errno);
        }
        atomic_store_explicit(&p->head.is_working, false, memory_order_release);
        LIST_REMOVE_ATOMIC_COUNTER(
            dp->executors.working, p, &dp->head.executors.working);
        monad_c_result r = monad_c_make_success(0);
        if (!atomic_load_explicit(&p->please_quit, memory_order_acquire)) {
            atomic_store_explicit(&p->head.is_idle, true, memory_order_release);
            LIST_APPEND_ATOMIC_COUNTER(
                dp->executors.idle, p, &dp->head.executors.idle);
            r = monad_c_make_success(-1);
        }
        if (dp->workloads_changed_waiting > 0) {
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_signal(&dp->lock, 0);
#endif
            cnd_broadcast(&dp->workloads_changed);
#if MONAD_HAVE_TSAN
            __tsan_mutex_post_signal(&dp->lock, 0);
#endif
        }
        if (thrd_success != mutex_unlock(&dp->lock)) {
            return monad_c_make_failure(errno);
        }
        return r;
    }
    return monad_c_make_success(0);
}

monad_c_result monad_async_work_dispatcher_executor_wake(
    monad_async_work_dispatcher_executor ex,
    monad_c_result const *cause_run_to_return)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    return monad_async_executor_wake(&p->derived.head, cause_run_to_return);
}

monad_c_result monad_async_work_dispatcher_submit(
    monad_async_work_dispatcher dp_, monad_async_task *tasks_, size_t count)
{
    if (count == 0) {
        return monad_c_make_success(0);
    }
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)dp_;
    struct monad_async_task_impl **tasks =
        (struct monad_async_task_impl **)tasks_;
    intptr_t added = 0, subtracted = 0;
    if (thrd_success != mutex_lock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    {
        struct monad_async_task_impl **tasksp =
            (struct monad_async_task_impl **)tasks;
        do {
            if (*tasksp == nullptr) {
                tasksp++;
                continue;
            }
            if ((*tasksp)->head.derived.user_code == nullptr ||
                atomic_load_explicit(
                    &(*tasksp)->head.current_executor, memory_order_acquire) !=
                    nullptr ||
                atomic_load_explicit(
                    &(*tasksp)->head.is_awaiting_dispatch,
                    memory_order_acquire) == true) {
                (void)mutex_unlock(&dp->lock);
                return monad_c_make_failure(EINVAL);
            }
            (*tasksp)->head.ticks_when_submitted =
                get_ticks_count(memory_order_relaxed);
            LIST_APPEND_ATOMIC_COUNTER(
                dp->tasks_awaiting_dispatch
                    [monad_async_task_effective_cpu_priority(*tasksp)],
                *tasksp,
                &dp->head.tasks_awaiting_dispatch);
            atomic_store_explicit(
                &(*tasksp)->head.is_awaiting_dispatch,
                true,
                memory_order_release);
            tasksp++;
            added++;
        }
        while (tasksp - tasks < (long int)count);
    }
    if (atomic_load_explicit(&dp->head.executors.idle, memory_order_relaxed) >
        0) {
        struct monad_async_work_dispatcher_executor_impl *ex =
            dp->executors.idle.front;
        for (monad_async_priority n = monad_async_priority_high;
             n < monad_async_priority_max;
             n++) {
            if (dp->tasks_awaiting_dispatch[n].count > 0) {
                for (; ex != nullptr &&
                       atomic_load_explicit(
                           &ex->please_quit, memory_order_acquire);
                     ex = ex->next) {
                }
                if (ex == nullptr) {
                    break;
                }
                struct monad_async_task_impl *item =
                    dp->tasks_awaiting_dispatch[n].front;
                // item->head.is_awaiting_dispatch is set to false by attach op
                LIST_REMOVE_ATOMIC_COUNTER(
                    dp->tasks_awaiting_dispatch[n],
                    item,
                    &dp->head.tasks_awaiting_dispatch);
                monad_c_result r = monad_async_task_attach(
                    &ex->derived.head, &item->head, nullptr);
                // Failure here is likely a logic error
                MONAD_CONTEXT_CHECK_RESULT(r);
                struct monad_async_work_dispatcher_executor_impl *p = ex;
                ex = ex->next;
                atomic_store_explicit(
                    &p->head.is_idle, false, memory_order_release);
                LIST_REMOVE_ATOMIC_COUNTER(
                    dp->executors.idle, p, &dp->head.executors.idle);
                atomic_store_explicit(
                    &p->head.is_working, true, memory_order_release);
                LIST_APPEND_ATOMIC_COUNTER(
                    dp->executors.working, p, &dp->head.executors.working);
                subtracted--;
            }
        }
    }
    if (subtracted > 0 && dp->workloads_changed_waiting > 0) {
#if MONAD_HAVE_TSAN
        __tsan_mutex_pre_signal(&dp->lock, 0);
#endif
        cnd_broadcast(&dp->workloads_changed);
#if MONAD_HAVE_TSAN
        __tsan_mutex_post_signal(&dp->lock, 0);
#endif
    }
    if (thrd_success != mutex_unlock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    return monad_c_make_success(added - subtracted);
}

monad_c_result monad_async_work_dispatcher_wait(
    monad_async_work_dispatcher dp_, size_t max_undispatched,
    size_t max_unexecuted, struct timespec *timeout)
{
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)dp_;
    monad_c_result r = monad_c_make_success(0);
    int64_t deadline = 0;
    if (timeout != nullptr && (timeout->tv_sec != 0 || timeout->tv_nsec != 0)) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
        deadline = timespec_to_ns(&now) + timespec_to_ns(timeout);
    }
    if (thrd_success != mutex_lock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    for (;;) {
        bool done = true;
        size_t unexecuted = atomic_load_explicit(
            &dp->head.tasks_awaiting_dispatch, memory_order_relaxed);
        if (unexecuted > max_undispatched) {
            done = false;
        }
        else if (max_unexecuted != (size_t)-1) {
            for (struct monad_async_work_dispatcher_executor_impl *ex =
                     dp->executors.working.front;
                 ex != nullptr;
                 ex = ex->next) {
                unexecuted += ex->derived.head.tasks_pending_launch +
                              ex->derived.head.tasks_suspended;
            }
            if (unexecuted > max_unexecuted) {
                done = false;
            }
        }
        if (done) {
            break;
        }
        dp->workloads_changed_waiting++;
        int ec = thrd_success;
        if (timeout == nullptr) {
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_unlock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_unlock(&dp->lock, __tsan_mutex_try_lock);
#endif
            ec = cnd_wait(&dp->workloads_changed, &dp->lock);
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_lock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_lock(&dp->lock, __tsan_mutex_try_lock, 0);
#endif
        }
        else if (deadline != 0) {
            struct timespec now;
            clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
            int64_t remaining = deadline - timespec_to_ns(&now);
            if (remaining <= 0) {
                r = monad_c_make_failure(ETIME);
                break;
            }
            struct timespec portion = {
                .tv_sec = remaining / 1000000000LL,
                .tv_nsec = remaining % 1000000000LL};
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_unlock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_unlock(&dp->lock, __tsan_mutex_try_lock);
#endif
            ec = cnd_timedwait(&dp->workloads_changed, &dp->lock, &portion);
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_lock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_lock(&dp->lock, __tsan_mutex_try_lock, 0);
#endif
        }
        dp->workloads_changed_waiting--;
        if (ec == thrd_error) {
            r = monad_c_make_failure(errno);
            break;
        }
    }
    if (thrd_success != mutex_unlock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    return r;
}

monad_c_result monad_async_work_dispatcher_quit(
    monad_async_work_dispatcher dp_, size_t max_executors,
    struct timespec *timeout)
{
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)dp_;
    monad_c_result r = monad_c_make_success(0);
    if (atomic_load_explicit(&dp->head.executors.idle, memory_order_relaxed) +
            atomic_load_explicit(
                &dp->head.executors.working, memory_order_relaxed) <=
        max_executors) {
        return r;
    }
    int64_t deadline = 0;
    if (timeout != nullptr && (timeout->tv_sec != 0 || timeout->tv_nsec != 0)) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
        deadline = timespec_to_ns(&now) + timespec_to_ns(timeout);
    }
    if (thrd_success != mutex_lock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    monad_c_result const cancelled = monad_c_make_failure(ECANCELED);
    for (;;) {
        int togo =
            (int)(atomic_load_explicit(
                      &dp->head.executors.idle, memory_order_relaxed) +
                  atomic_load_explicit(
                      &dp->head.executors.working, memory_order_relaxed)) -
            (int)max_executors;
        if (togo <= 0) {
            break;
        }
        struct monad_async_work_dispatcher_executor_impl *ex =
            dp->executors.idle.front;
        while (ex != nullptr && togo > 0) {
            for (;
                 ex != nullptr &&
                 atomic_load_explicit(&ex->please_quit, memory_order_acquire) &&
                 togo > 0;
                 ex = ex->next) {
                togo--;
            }
            if (ex != nullptr && togo > 0) {
                atomic_store_explicit(
                    &ex->please_quit, true, memory_order_release);
                togo--;
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    (void)mutex_unlock(&dp->lock),
                    monad_async_executor_wake(&ex->derived.head, &cancelled));
            }
        }
        ex = dp->executors.working.front;
        while (ex != nullptr && togo > 0) {
            for (;
                 ex != nullptr &&
                 atomic_load_explicit(&ex->please_quit, memory_order_acquire) &&
                 togo > 0;
                 ex = ex->next) {
                togo--;
            }
            if (ex != nullptr && togo > 0) {
                atomic_store_explicit(
                    &ex->please_quit, true, memory_order_release);
                togo--;
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    (void)mutex_unlock(&dp->lock),
                    monad_async_executor_wake(&ex->derived.head, &cancelled));
            }
        }
        dp->workloads_changed_waiting++;
        int ec = thrd_success;
        if (timeout == nullptr) {
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_unlock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_unlock(&dp->lock, __tsan_mutex_try_lock);
#endif
            ec = cnd_wait(&dp->workloads_changed, &dp->lock);
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_lock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_lock(&dp->lock, __tsan_mutex_try_lock, 0);
#endif
        }
        else if (deadline != 0) {
            struct timespec now;
            clock_gettime(CLOCK_MONOTONIC_COARSE, &now);
            int64_t remaining = deadline - timespec_to_ns(&now);
            if (remaining <= 0) {
                r = monad_c_make_failure(ETIME);
                break;
            }
            struct timespec portion = {
                .tv_sec = remaining / 1000000000LL,
                .tv_nsec = remaining % 1000000000LL};
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_unlock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_unlock(&dp->lock, __tsan_mutex_try_lock);
#endif
            ec = cnd_timedwait(&dp->workloads_changed, &dp->lock, &portion);
#if MONAD_HAVE_TSAN
            __tsan_mutex_pre_lock(&dp->lock, __tsan_mutex_try_lock);
            __tsan_mutex_post_lock(&dp->lock, __tsan_mutex_try_lock, 0);
#endif
        }
        dp->workloads_changed_waiting--;
        if (ec == thrd_error) {
            r = monad_c_make_failure(errno);
            break;
        }
    }
    if (thrd_success != mutex_unlock(&dp->lock)) {
        return monad_c_make_failure(errno);
    }
    return r;
}
