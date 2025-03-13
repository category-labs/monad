#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <latch>
#include <numeric>
#include <thread>
#include <vector>

#include <pthread.h>
#include <sched.h>

#include <gtest/gtest.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/spinloop.h>

constexpr unsigned NUM_THREADS = 4;

struct shared_state
{
    alignas(64) monad_spinlock_t lock;
    uint64_t counter;
    uint64_t thread_count[NUM_THREADS];
    alignas(64) std::atomic<unsigned> done;
};

#if NDEBUG
constexpr unsigned ITER_MAX = 1 << 22;
#else
constexpr unsigned ITER_MAX = 1 << 18;
#endif

static void
lock_thread_function(shared_state &s, unsigned value, std::latch &latch)
{
    latch.arrive_and_wait();
    while (true) {
        MONAD_SPINLOCK_LOCK(&s.lock);
        ASSERT_TRUE(monad_spinlock_is_self_owned(&s.lock));
        if (s.counter == ITER_MAX) [[unlikely]] {
            MONAD_SPINLOCK_UNLOCK(&s.lock);
            s.done.fetch_add(1);
            return;
        }
        if (s.counter % NUM_THREADS == value) {
            ++s.counter;
            ++s.thread_count[value];
        }
        MONAD_SPINLOCK_UNLOCK(&s.lock);
    }
}

static void
try_lock_thread_function(shared_state &s, unsigned value, std::latch &latch)
{
    latch.arrive_and_wait();
    while (true) {
        while (!MONAD_SPINLOCK_TRY_LOCK(&s.lock)) {
            monad_spinloop_hint();
        }
        ASSERT_TRUE(monad_spinlock_is_self_owned(&s.lock));
        if (s.counter == ITER_MAX) [[unlikely]] {
            MONAD_SPINLOCK_UNLOCK(&s.lock);
            s.done.fetch_add(1);
            return;
        }
        if (s.counter % NUM_THREADS == value) {
            ++s.counter;
            ++s.thread_count[value];
        }
        MONAD_SPINLOCK_UNLOCK(&s.lock);
    }
}

static int alloc_next_free_cpu(cpu_set_t *cpus, int start)
{
    for (int i = start; i < CPU_SETSIZE; ++i) {
        if (CPU_ISSET(i, cpus)) {
            CPU_CLR(i, cpus);
            return i;
        }
    }
    return -1;
}

static void pin_threads_to_cores(std::vector<std::thread> &threads)
{
    cpu_set_t proc_affinity;
    cpu_set_t free_cpus;
    ASSERT_EQ(0, sched_getaffinity(0, sizeof proc_affinity, &proc_affinity));
    ASSERT_LT(NUM_THREADS, CPU_COUNT(&proc_affinity));

    CPU_ZERO(&free_cpus);
    CPU_OR(&free_cpus, &proc_affinity, &free_cpus);

    int cpu_id = 1;
    for (std::thread &thr : threads) {
        cpu_set_t thread_set;
        CPU_ZERO(&thread_set);
        cpu_id = alloc_next_free_cpu(&free_cpus, cpu_id);
        MONAD_ASSERT(cpu_id != -1);
        CPU_SET(cpu_id++, &thread_set);
        ASSERT_EQ(
            0,
            pthread_setaffinity_np(
                thr.native_handle(), sizeof thread_set, &thread_set));
    }
}

// A basic test of the spinlock, where two threads fight for the lock. This
// deliberately does not use std::this_thread::yield(), so that more lock
// contention is caused. This allows it to double as a performance test, but
// the statistics are not stable unless ITER_MAX is set to a higher number,
// like 1 << 29 (normally we can't wait that long in the automated test suite)
TEST(spinlock, lock_basic)
{
    shared_state s{};
    std::latch latch{NUM_THREADS + 1};
    monad_spinlock_init(&s.lock);
    ASSERT_TRUE(monad_spinlock_is_unowned(&s.lock));

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < NUM_THREADS; ++i) {
        threads.emplace_back(
            lock_thread_function, std::ref(s), i, std::ref(latch));
    }
    pin_threads_to_cores(threads);

    latch.arrive_and_wait();
    auto const start_time = std::chrono::system_clock::now();
    while (s.done.load(std::memory_order::acquire) < NUM_THREADS) {
        monad_spinloop_hint();
    }
    auto const end_time = std::chrono::system_clock::now();
    for (std::thread &t : threads) {
        t.join();
    }

    uint64_t const total = std::accumulate(
        std::begin(s.thread_count), std::end(s.thread_count), 0UL);
    ASSERT_EQ(ITER_MAX, total);

    // Average time it takes for the odd or even thread to make its update.
    // This is essentially a measure of lock contention.
    auto const avg_cycle_time =
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                end_time - start_time)
                .count()) /
        s.counter;
    std::fprintf(
        stdout,
        "avg. cycle time: %lu\n",
        static_cast<unsigned long>(avg_cycle_time));
}

TEST(spinlock, try_lock_basic)
{
    shared_state s{};
    std::latch latch{NUM_THREADS + 1};
    monad_spinlock_init(&s.lock);
    ASSERT_TRUE(monad_spinlock_is_unowned(&s.lock));

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < NUM_THREADS; ++i) {
        threads.emplace_back(
            try_lock_thread_function, std::ref(s), i, std::ref(latch));
    }
    pin_threads_to_cores(threads);

    latch.arrive_and_wait();
    auto const start_time = std::chrono::system_clock::now();
    while (s.done.load(std::memory_order::acquire) < NUM_THREADS) {
        monad_spinloop_hint();
    }
    auto const end_time = std::chrono::system_clock::now();
    for (std::thread &t : threads) {
        t.join();
    }

    uint64_t const total = std::accumulate(
        std::begin(s.thread_count), std::end(s.thread_count), 0UL);
    ASSERT_EQ(ITER_MAX, total);

    // Average time it takes for the odd or even thread to make its update.
    // This is essentially a measure of lock contention.
    auto const avg_cycle_time =
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                end_time - start_time)
                .count()) /
        s.counter;
    std::fprintf(
        stdout,
        "avg. cycle time: %lu\n",
        static_cast<unsigned long>(avg_cycle_time));
}
