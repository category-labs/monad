#include "current.h"

static void _main_fiber_resume(struct monad_fiber_task *const this)
{
    monad_fiber_switch_to_fiber((monad_fiber_t *const)this);
}

static void _main_fiber_destroy(struct monad_fiber_task *const this)
{
    (void)this;
    pthread_exit(NULL);
}

thread_local monad_fiber_t monad_fiber_main_fiber_ = {
    .task = {.resume = &_main_fiber_resume, .destroy = &_main_fiber_destroy},
    .context = NULL,
    .scheduler = NULL};

thread_local monad_fiber_t *monad_fiber_current_ = NULL;

bool monad_fiber_is_main(monad_fiber_t *const this)
{
    return this->task.destroy == _main_fiber_destroy;
}
