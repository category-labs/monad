#pragma once

#include "task.h"

#if defined(__cplusplus)
    #include <atomic>

extern "C"
{
#else
    #include <stdatomic.h>

#endif

#include <pthread.h>

#include <assert.h>
#include <errno.h>
#include <malloc.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

typedef struct monad_fiber_scheduler
{
    pthread_t *threads;
    size_t thread_count;
    pthread_mutex_t mutex;
    pthread_cond_t cond;

    monad_fiber_task_queue_t task_queue;
#if defined(__cplusplus)
    std::
#endif
        atomic_int thread_id_source; // if this is zero we're stoppping

    // function to call on creation of every thread (meant for
    // monad_fiber_init_main)
    void (*init_thread)();
} monad_fiber_scheduler_t;

monad_fiber_scheduler_t *monad_fiber_scheduler_current();

void monad_fiber_scheduler_work(monad_fiber_scheduler_t *);
void monad_fiber_scheduler_create(
    monad_fiber_scheduler_t *, size_t threads, void (*init_thread)());
void monad_fiber_scheduler_destroy(monad_fiber_scheduler_t *);
void monad_fiber_scheduler_stop(monad_fiber_scheduler_t *);

void monad_fiber_scheduler_post(
    monad_fiber_scheduler_t *, monad_fiber_task_t *task);
// does not yet respect priorities. we should figure out if we need this
// function first.
void monad_fiber_scheduler_dispatch(
    monad_fiber_scheduler_t *, monad_fiber_task_t *task);

monad_fiber_task_t *monad_fiber_scheduler_pop_higher_priority_task(
    monad_fiber_scheduler_t *, int64_t priority);

bool monad_fiber_run_one(monad_fiber_scheduler_t *);

#if defined(__cplusplus)
}
#endif
