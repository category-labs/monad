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

#include <category/core/fiber/fiber_group.hpp>
#include <category/core/fiber/fiber_thread_pool.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/fiber/future.hpp>
#include <boost/fiber/operations.hpp>
#ifdef __clang__
    #pragma clang diagnostic pop
#endif

#include <atomic>
#include <chrono>
#include <memory>
#include <thread>

using namespace monad::fiber;

// Test that two fiber groups can share the same thread pool and submit work
// between each other without deadlock.
TEST(FiberGroup, shared_thread_pool_cross_submit)
{
    // Create a thread pool with 4 threads
    auto thread_pool = std::make_unique<FiberThreadPool>(4, true);

    // Create two fiber groups sharing the same thread pool
    auto group1 = thread_pool->create_fiber_group(2);
    auto group2 = thread_pool->create_fiber_group(2);

    std::atomic<int> group1_count{0};
    std::atomic<int> group2_count{0};
    std::atomic<int> cross_submit_count{0};

    // Submit work to group1 that will submit work to group2
    for (int i = 0; i < 10; ++i) {
        group1->submit(1, [&, i](auto const &) {
            group1_count.fetch_add(1, std::memory_order_relaxed);

            // Submit work to group2 from within group1's fiber
            auto const promise =
                std::make_shared<boost::fibers::promise<int>>();
            auto future = promise->get_future();

            group2->submit(1, [&, i, promise](auto const &) {
                group2_count.fetch_add(1, std::memory_order_relaxed);
                cross_submit_count.fetch_add(1, std::memory_order_relaxed);
                promise->set_value(i * 2);
            });

            // Wait for the result from group2
            auto const result = future.get();
            EXPECT_EQ(result, i * 2);
        });
    }

    // Also submit work directly to group2
    for (int i = 0; i < 5; ++i) {
        group2->submit(1, [&](auto const &) {
            group2_count.fetch_add(1, std::memory_order_relaxed);
        });
    }

    // Wait for all work to complete by destroying the groups
    // (destructor waits for all fibers to finish)
    group1.reset();
    group2.reset();

    // Verify all work was executed
    EXPECT_EQ(group1_count.load(), 10);
    EXPECT_EQ(group2_count.load(), 15); // 10 from cross-submit + 5 direct
    EXPECT_EQ(cross_submit_count.load(), 10);
}

// Test that demonstrates the deadlock scenario that would occur if we
// didn't separate fiber groups
TEST(FiberGroup, multiple_groups_prevent_deadlock)
{
    // Create thread pool with limited threads
    auto thread_pool = std::make_unique<FiberThreadPool>(2, true);

    // Create two groups: one for "outer" work and one for "inner" work
    auto outer_group = thread_pool->create_fiber_group(2);
    auto inner_group = thread_pool->create_fiber_group(4);

    std::atomic<int> completed{0};

    // Submit multiple outer tasks that each spawn inner tasks
    // This simulates trace_block submitting to trace_tx_exec
    for (int i = 0; i < 4; ++i) {
        outer_group->submit(1, [&](auto const &) {
            auto const promise =
                std::make_shared<boost::fibers::promise<void>>();
            auto const future = promise->get_future();

            // Submit inner work (like executing transactions)
            inner_group->submit(1, [&, promise](auto const &) {
                // Simulate some work
                boost::this_fiber::sleep_for(std::chrono::milliseconds(10));
                promise->set_value();
            });

            // Wait for inner work to complete
            future.wait();
            completed.fetch_add(1, std::memory_order_relaxed);
        });
    }

    // Clean up groups (waits for completion)
    outer_group.reset();
    inner_group.reset();

    // All tasks should complete without deadlock
    EXPECT_EQ(completed.load(), 4);
}

// Test concurrent access to multiple fiber groups
TEST(FiberGroup, concurrent_multi_group_access)
{
    auto thread_pool = std::make_unique<FiberThreadPool>(4, true);

    auto group1 = thread_pool->create_fiber_group(8);
    auto group2 = thread_pool->create_fiber_group(8);
    auto group3 = thread_pool->create_fiber_group(8);

    std::atomic<int> total_work{0};
    constexpr int work_per_group = 100;

    // Submit work to all three groups concurrently
    auto submit_work = [&](FiberGroup &group) {
        for (int i = 0; i < work_per_group; ++i) {
            group.submit(1, [&](auto const &) {
                total_work.fetch_add(1, std::memory_order_relaxed);
            });
        }
    };

    std::thread t1([&] { submit_work(*group1); });
    std::thread t2([&] { submit_work(*group2); });
    std::thread t3([&] { submit_work(*group3); });

    t1.join();
    t2.join();
    t3.join();

    // Wait for all work to complete
    group1.reset();
    group2.reset();
    group3.reset();

    EXPECT_EQ(total_work.load(), work_per_group * 3);
}
