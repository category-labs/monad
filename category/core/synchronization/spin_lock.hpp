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

#include <category/core/config.hpp>

#include <atomic>
#include <string>

MONAD_NAMESPACE_BEGIN

class SpinLock
{
    /// CONSTANTS
    static constexpr uint64_t backoff_count = 100;
    static constexpr uint64_t backoff_start = 100;

    /// DATA
    std::atomic<bool> state_{false};

/// STATS MACROS
#ifdef MONAD_SPIN_LOCK_STATS
    #define STATS_EVENT_TRY(x) stats_.event_try(x)
    #define STATS_EVENT_LOCK(x) stats_.event_lock(x)
#else
    #define STATS_EVENT_TRY(x)
    #define STATS_EVENT_LOCK(x)
#endif

public:
    bool try_lock()
    {
        bool const res = try_lock_impl();
        STATS_EVENT_TRY(res);
        return res;
    }

    void lock()
    {
        bool const res = try_lock_impl();
        if (!res) {
            lock_impl_slow();
        }
        STATS_EVENT_LOCK(res);
    }

    void unlock()
    {
        state_.store(false, std::memory_order_release);
    }

private:
    bool try_lock_impl()
    {
        return !state_.exchange(true, std::memory_order_acquire);
    }

    void lock_impl_slow()
    {
        uint64_t spin = 0;
        do {
            while (state_.load(std::memory_order_relaxed)) {
                if (++spin > backoff_start) {
                    backoff();
                }
            }
        }
        while (!try_lock_impl());
    }

    void backoff()
    {
#ifdef __x86_64__
        __builtin_ia32_pause();
#else
        for (uint64_t i = 0; i < backoff_count; ++i) {
            __asm__ __volatile__("" : : : "memory");
        }
#endif
    }

/// STATS
#undef STATS_EVENT_TRY
#undef STATS_EVENT_LOCK

public:
    std::string print_stats()
    {
        std::string str;
#ifdef MONAD_SPIN_LOCK_STATS
        str = stats_.print_stats();
#endif
        return str;
    }

private:
#ifdef MONAD_SPIN_LOCK_STATS
    struct LockStats
    {
        std::atomic<uint64_t> n_try_busy_{0};
        uint64_t n_try_free_{0};
        uint64_t n_lock_busy_{0};
        uint64_t n_lock_free_{0};

        void event_try(bool res)
        {
            if (res) {
                ++n_try_free_;
            }
            else {
                n_try_busy_.fetch_add(1, std::memory_order_release);
            }
        }

        void event_lock(bool res)
        {
            if (res) {
                ++n_lock_free_;
            }
            else {
                ++n_lock_busy_;
            }
        }

        std::string print_stats()
        {
            char str[100];
            sprintf(
                str,
                " %4ld %4ld",
                n_try_free_ + n_lock_free_,
                n_try_busy_.load() + n_lock_busy_);
            clear_stats();
            return std::string(str);
        }

        void clear_stats()
        {
            n_try_free_ = 0;
            n_try_busy_.store(0);
            n_lock_free_ = 0;
            n_lock_busy_ = 0;
        }
    }; /// LockStats

    LockStats stats_;
#endif // MONAD_SPIN_LOCK_STATS

}; /// SpinLock

MONAD_NAMESPACE_END
