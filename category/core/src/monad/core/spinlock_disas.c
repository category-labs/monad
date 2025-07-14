#include <monad/core/spinlock.h>

void spinlock_init_disas(spinlock_t *const lock)
{
    spinlock_init(lock);
}

bool spinlock_try_lock_disas(spinlock_t *const lock)
{
    return spinlock_try_lock(lock);
}

void spinlock_lock_disas(spinlock_t *const lock)
{
    spinlock_lock(lock);
}

void spinlock_unlock_disas(spinlock_t *const lock)
{
    spinlock_unlock(lock);
}
