#include "scheduler.h"

#include "assert.h"

#include <pthread.h>

thread_local monad_fiber_scheduler_t *monad_fiber_scheduler_current_ = NULL;

monad_fiber_scheduler_t *monad_fiber_scheduler_current()
{
    return monad_fiber_scheduler_current_;
}

static void *work(void *this_)
{
    monad_fiber_scheduler_t *this = (monad_fiber_scheduler_t *)this_;
    monad_fiber_scheduler_work(this);
    return NULL;
}

void monad_fiber_scheduler_create(
    monad_fiber_scheduler_t *this, size_t threads, void (*init_thread)())
{
    this->threads = malloc(sizeof(pthread_t) * threads);
    this->thread_count = threads;
    this->init_thread = init_thread;
    MONAD_CCALL_ASSERT(pthread_mutex_init(&this->mutex, NULL));
    MONAD_CCALL_ASSERT(pthread_cond_init(&this->cond, NULL));

    this->thread_id_source = 1;
    monad_fiber_task_queue_init(&this->task_queue);

    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

    for (size_t i = 0u; i < threads; i++) {
        MONAD_CCALL_ASSERT(pthread_create(this->threads + i, NULL, work, this));
    }

    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}

void monad_fiber_scheduler_destroy(monad_fiber_scheduler_t *this)
{
    monad_fiber_scheduler_stop(this);

    for (size_t i = 0u; i < this->thread_count; i++) {
        MONAD_CCALL_ASSERT(pthread_join(this->threads[i], NULL));
    }

    free(this->threads);
    monad_fiber_task_queue_destroy(&this->task_queue);
    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
    MONAD_CCALL_ASSERT(pthread_cond_destroy(&this->cond));
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}

void monad_fiber_scheduler_post(
    monad_fiber_scheduler_t *this, monad_fiber_task_t *task)
{
    MONAD_ASSERT(task != 0);
    MONAD_DEBUG_ASSERT(this != 0);
    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

    monad_fiber_task_queue_insert(&this->task_queue, task);
    MONAD_CCALL_ASSERT(pthread_cond_signal(&this->cond));
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}

void monad_fiber_scheduler_dispatch(
    monad_fiber_scheduler_t *this, monad_fiber_task_t *task)
{
    if (this == monad_fiber_scheduler_current_) // check priority
    {
        task->resume(task);
    }
    else {
        monad_fiber_scheduler_post(this, task);
    }
}

void monad_fiber_scheduler_stop(monad_fiber_scheduler_t *this)
{
    this->thread_id_source = 0;
    MONAD_CCALL_ASSERT(pthread_cond_broadcast(&this->cond));
}

void monad_fiber_scheduler_work(monad_fiber_scheduler_t *this)
{
    monad_fiber_scheduler_current_ = this;
    if (this->thread_id_source != 0) {
        char name[24];
        snprintf(name, 24, "worker thread %u", ++(this->thread_id_source));
        MONAD_CCALL_ASSERT(pthread_setname_np(pthread_self(), name));
    }

    if (this->init_thread != NULL) {
        (*this->init_thread)();
    }

    while (this->thread_id_source > 0) {
        MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
        while (this->task_queue.size == 0u) {
            if (this->thread_id_source != 0) {
                MONAD_CCALL_ASSERT(
                    pthread_cond_wait(&this->cond, &this->mutex));
            }
            if (this->thread_id_source == 0) {
                while (this->task_queue.size > 0u) {
                    monad_fiber_task_t *t =
                        monad_fiber_task_queue_pop_front(&this->task_queue);
                    t->destroy(t);
                }
                MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
                return;
            }
        }

        if (this->task_queue.size == 0u) {
            MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
            continue;
        }

        monad_fiber_task_t *t =
            monad_fiber_task_queue_pop_front(&this->task_queue);
        MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
        t->resume(t);
    }
    monad_fiber_scheduler_current_ = NULL;
}

monad_fiber_task_t *monad_fiber_scheduler_pop_higher_priority_task(
    monad_fiber_scheduler_t *this, int64_t priority)
{
    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

    monad_fiber_task_t *result = NULL;
    // check if the first element is
    if (this->task_queue.size > 0 &&
        (*this->task_queue.data)->priority < priority) {
        result = monad_fiber_task_queue_pop_front(&this->task_queue);
    }

    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return result;
}

bool monad_fiber_run_one(monad_fiber_scheduler_t *this)
{
    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
    monad_fiber_task_t *node = NULL;
    if (this->task_queue.size != 0u) {
        node = monad_fiber_task_queue_pop_front(&this->task_queue);
    }
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    if (node != NULL) {
        node->resume(node);
        return true;
    }
    else {
        return false;
    }
}
