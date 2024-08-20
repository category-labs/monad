#include <monad/core/spinlock.h>

void spinlock_init_disas(monad_spinlock_t *const lock)
{
    monad_spinlock_init(lock);
}

bool spinlock_try_lock_disas(monad_spinlock_t *const lock)
{
    return monad_spinlock_try_lock(lock);
}

void spinlock_lock_disas(monad_spinlock_t *const lock)
{
    monad_spinlock_lock(lock);
}

void spinlock_unlock_disas(monad_spinlock_t *const lock)
{
    monad_spinlock_unlock(lock);
}
