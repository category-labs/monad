// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/cpu_relax.h>
#include <category/core/likely.h>
#include <category/core/tl_tid.h>

#include <assert.h>
#include <stdatomic.h>
#include <stdbool.h>

static_assert(ATOMIC_INT_LOCK_FREE == 2);

typedef atomic_int spinlock_t;

static inline void spinlock_init(spinlock_t *const lock)
{
    atomic_init(lock, 0);
}

static inline bool spinlock_try_lock(spinlock_t *const lock)
{
    int expected = 0;
    int const desired = get_tl_tid();
    return atomic_compare_exchange_weak_explicit(
        lock, &expected, desired, memory_order_acquire, memory_order_relaxed);
}

static inline void spinlock_lock(spinlock_t *const lock)
{
    int const desired = get_tl_tid();
    for (;;) {
        /**
         * TODO further analysis of retry logic
         * - if weak cmpxch fails, spin again or cpu relax?
         * - compare intel vs arm
         * - benchmark with real use cases
        */
        unsigned retries = 0;
        while (
            MONAD_UNLIKELY(atomic_load_explicit(lock, memory_order_relaxed))) {
            if (MONAD_LIKELY(retries < 128)) {
                ++retries;
            }
            else {
                cpu_relax();
            }
        }
        int expected = 0;
        if (MONAD_LIKELY(atomic_compare_exchange_weak_explicit(
                lock,
                &expected,
                desired,
                memory_order_acquire,
                memory_order_relaxed))) {
            break;
        }
    }
}

static inline void spinlock_unlock(spinlock_t *const lock)
{
    atomic_store_explicit(lock, 0, memory_order_release);
}
