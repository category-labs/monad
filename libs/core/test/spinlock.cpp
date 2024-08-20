#include <chrono>
#include <cstdio>
#include <thread>

#include <gtest/gtest.h>

#include <monad/core/spinlock.h>

struct shared_state
{
    monad_spinlock_t lock;
    unsigned counter;
    unsigned odd_count;
    unsigned even_count;
};

#if NDEBUG
constexpr unsigned ITER_MAX = 1 << 22;
#else
constexpr unsigned ITER_MAX = 1 << 20;
#endif

static void thread_function(shared_state &s)
{
    while (true) {
        MONAD_SPINLOCK_LOCK(&s.lock);
        ASSERT_TRUE(monad_spinlock_is_owned(&s.lock));
        if (s.counter == ITER_MAX) [[unlikely]] {
            MONAD_SPINLOCK_UNLOCK(&s.lock);
            return;
        }
        if (s.counter % 2 == 0) {
            ++s.counter;
            ++s.odd_count;
        }
        MONAD_SPINLOCK_UNLOCK(&s.lock);
    }
}

// A basic test of the spinlock, where two threads fight for the lock. This
// deliberately does not use std::this_thread::yield(), so that more lock
// contention is caused. This allows it to double as a performance test, but
// the statistics are not stable unless ITER_MAX is set to a higher number
// (normally we don't want to wait that long in the test suite)
TEST(spinlock, basic)
{
    shared_state s{};
    bool done;
    monad_spinlock_init(&s.lock);
    ASSERT_TRUE(monad_spinlock_is_unowned(&s.lock));

    auto const start_time = std::chrono::system_clock::now();
    std::thread thr{thread_function, std::ref(s)};
    do {
        MONAD_SPINLOCK_LOCK(&s.lock);
        ASSERT_TRUE(monad_spinlock_is_owned(&s.lock));
        if (s.counter % 2 == 1) {
            ++s.counter;
            ++s.even_count;
        }
        done = s.counter == ITER_MAX;
        MONAD_SPINLOCK_UNLOCK(&s.lock);
    }
    while (!done);
    auto const end_time = std::chrono::system_clock::now();

    thr.join();
    ASSERT_EQ(s.counter / 2, s.odd_count);
    ASSERT_EQ(s.counter / 2, s.even_count);

    // Average time it takes for the odd or even thread to make its update.
    // This is essentially a measure of lock contention.
    auto const avg_cycle_time =
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            end_time - start_time)
            .count() /
        s.counter;
    std::fprintf(
        stdout,
        "avg. cycle time: %lu\n",
        static_cast<unsigned long>(avg_cycle_time));
}
