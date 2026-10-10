// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/fiber/priority_pool.hpp>
#include <category/core/thread_idle.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <array>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <thread>

using namespace monad;

namespace
{
    std::map<std::string, uint64_t> fiber_pool_idle()
    {
        std::array<ThreadIdleSample, ThreadIdleRegistry::MAX_THREADS> out;
        size_t const n = ThreadIdleRegistry::global().snapshot(out);
        std::map<std::string, uint64_t> by_name;
        for (size_t i = 0; i < n; ++i) {
            std::string const name{out[i].name.data()};
            if (name.starts_with("ftpool ")) {
                by_name[name] += out[i].idle_ns;
            }
        }
        return by_name;
    }

    std::map<std::string, uint64_t> wait_for_workers(size_t const n)
    {
        auto const deadline =
            std::chrono::steady_clock::now() + std::chrono::seconds(5);
        auto idle = fiber_pool_idle();
        while (idle.size() < n && std::chrono::steady_clock::now() < deadline) {
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
            idle = fiber_pool_idle();
        }
        return idle;
    }

    constexpr auto WINDOW = std::chrono::milliseconds(500);
    constexpr uint64_t WINDOW_NS = 500'000'000;
}

TEST(FiberThreadPoolIdle, workers_register_under_their_thread_names)
{
    {
        fiber::PriorityPool const pool{2, 8};
        auto const idle = wait_for_workers(2);
        EXPECT_EQ(idle.size(), 2u);
        EXPECT_TRUE(idle.contains("ftpool 0"));
        EXPECT_TRUE(idle.contains("ftpool 1"));
    }
    EXPECT_TRUE(fiber_pool_idle().empty());
}

TEST(FiberThreadPoolIdle, an_idle_pool_is_idle_for_most_of_wall_time)
{
    fiber::PriorityPool const pool{2, 8};
    auto const before = wait_for_workers(2);
    ASSERT_EQ(before.size(), 2u);
    std::this_thread::sleep_for(WINDOW);
    auto const after = fiber_pool_idle();
    ASSERT_EQ(after.size(), 2u);
    for (auto const &[name, idle] : after) {
        EXPECT_GE(idle - before.at(name), WINDOW_NS * 8 / 10) << name;
    }
}

TEST(FiberThreadPoolIdle, a_saturated_pool_is_rarely_idle)
{
    fiber::PriorityPool pool{2, 8};
    ASSERT_EQ(wait_for_workers(2).size(), 2u);

    // Fibers are cooperative: one that never yields holds its thread busy.
    std::atomic<bool> stop{false};
    std::atomic<unsigned> running{0};
    std::atomic<unsigned> finished{0};
    for (int i = 0; i < 2; ++i) {
        pool.submit(0, [&] {
            running.fetch_add(1);
            while (!stop.load(std::memory_order_relaxed)) {
            }
            finished.fetch_add(1);
        });
    }
    while (running.load() < 2) {
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    auto const before = fiber_pool_idle();
    std::this_thread::sleep_for(WINDOW);
    auto const after = fiber_pool_idle();
    stop.store(true);
    while (finished.load() < 2) {
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }

    ASSERT_EQ(after.size(), 2u);
    for (auto const &[name, idle] : after) {
        EXPECT_LT(idle - before.at(name), WINDOW_NS / 5) << name;
    }
}

TEST(FiberThreadPoolIdle, pool_churn_leaves_no_stale_registrations)
{
    for (int i = 0; i < 20; ++i) {
        fiber::PriorityPool const pool{3, 4};
        ASSERT_EQ(wait_for_workers(3).size(), 3u);
    }
    EXPECT_TRUE(fiber_pool_idle().empty());
}
