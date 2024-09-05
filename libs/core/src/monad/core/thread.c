#include <monad/core/thread.h>

__thread monad_tid_t _monad_tl_tid = 0;

#if defined(__linux__)
#include <pthread.h>
#include <unistd.h>
static_assert(sizeof(monad_tid_t) >= sizeof(pid_t));

void _monad_tl_tid_init()
{
    _monad_tl_tid = gettid();
}

int monad_thread_set_name(char const *name)
{
    return pthread_setname_np(pthread_self(), name);
}
#endif

#if defined(__APPLE__)
#include <err.h>
#include <pthread.h>
#include <stdint.h>
static_assert(sizeof(monad_tid_t) >= sizeof(uint64_t));

void _monad_tl_tid_init()
{
    uint64_t tid;
    if (pthread_threadid_np(pthread_self(), &tid) != 0) {
        err(1, "init_tl_tid: pthread_threadid_np(3) failed");
    }
    _monad_tl_tid = (monad_tid_t)tid;
}

errno_t monad_thread_set_name(char const *name)
{
    pthread_setname_np(name);
    return 0;
}
#endif
