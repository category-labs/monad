#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdlib.h>
#include <sys/queue.h>
#include <threads.h>

#include <pthread.h>
#include <sysexits.h>

#include <monad/context/context_switcher.h>
#include <monad/core/c_result.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/tl_tid.h>
#include <monad/fiber/fiber.h>

// This structure keeps track of a global list of all active
// monad_thread_executor objects that exist in the process; this is used for
// debugging
static struct thr_exec_global_state
{
    monad_spinlock_t lock;
    pthread_key_t key;
    SLIST_HEAD(, monad_thread_executor) head;
    size_t count;
} g_thr_execs;

monad_context_switcher_impl const *g_monad_fiber_default_context_switcher_impl;
thread_local struct monad_thread_executor _monad_tl_thr_exec;
static thread_local monad_context_switcher_impl const
    *_monad_tl_context_switcher_impl;

static monad_context_switcher_impl const *get_thread_context_switcher_impl()
{
    monad_context_switcher_impl const *const impl =
        _monad_tl_context_switcher_impl;
    return impl != nullptr ? impl
                           : __atomic_load_n(
                                 &g_monad_fiber_default_context_switcher_impl,
                                 __ATOMIC_ACQUIRE);
}

static void monad_thread_executor_dtor(void *arg)
{
    monad_thread_executor_t *const thr_exec = arg;
    MONAD_SPINLOCK_LOCK(&g_thr_execs.lock);
    SLIST_REMOVE(&g_thr_execs.head, thr_exec, monad_thread_executor, next);
    --g_thr_execs.count;
    MONAD_SPINLOCK_UNLOCK(&g_thr_execs.lock);

    // XXX: destroy all linked contexts first? Can potentially only do this
    // if MONAD_CONTEXT_TRACK_OWNERSHIP is defined...
    if (atomic_load_explicit(
            &thr_exec->switcher->contexts, memory_order_acquire) == 0) {
        thr_exec->switcher->self_destroy(thr_exec->switcher);
    }
}

void _monad_init_thread_executor(monad_thread_executor_t *thr_exec)
{
    int rc;
    monad_c_result mcr;
    monad_context_switcher_impl const *const switcher_impl =
        get_thread_context_switcher_impl();

    memset(thr_exec, 0, sizeof *thr_exec);
    mcr = switcher_impl->create(&thr_exec->switcher);
    if (MONAD_FAILED(mcr)) {
        monad_errc(
            EX_SOFTWARE, mcr.error, "monad_switcher_impl->create() failed");
    }
    thr_exec->switcher->user_ptr = thr_exec;
    thr_exec->thread = thrd_current();
    thr_exec->thread_id = (uint64_t)get_tl_tid();

    MONAD_SPINLOCK_LOCK(&g_thr_execs.lock);
    SLIST_INSERT_HEAD(&g_thr_execs.head, thr_exec, next);
    ++g_thr_execs.count;
    rc = pthread_setspecific(g_thr_execs.key, thr_exec);
    if (rc != 0) {
        errno = rc;
        err(1, "pthread_setspecific(3) failed");
    }
    MONAD_SPINLOCK_UNLOCK(&g_thr_execs.lock);
}

static void __attribute((constructor)) init_fiber_global_state()
{
    int rc;

    monad_spinlock_init(&g_thr_execs.lock);
    rc = pthread_key_create(&g_thr_execs.key, monad_thread_executor_dtor);
    if (rc != 0) {
        errno = rc;
        err(1, "pthread_key_create(3) failed");
    }
    SLIST_INIT(&g_thr_execs.head);
    g_monad_fiber_default_context_switcher_impl =
        &monad_context_switcher_fcontext;
}

static void __attribute__((destructor)) cleanup_fiber_global_state()
{
    while (!SLIST_EMPTY(&g_thr_execs.head)) {
        monad_thread_executor_dtor(SLIST_FIRST(&g_thr_execs.head));
    }
    (void)pthread_key_delete(g_thr_execs.key);
}
