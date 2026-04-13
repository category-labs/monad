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

#include <category/core/fiber/priority_pool.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <boost/fiber/future.hpp>
#include <boost/fiber/operations.hpp>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <thread>
#include <vector>

using clock_type = std::chrono::steady_clock;

TEST(PriorityInversion, cross_thread_wakeup_latency)
{

    constexpr unsigned N_THREADS = 4;
    constexpr unsigned N_FIBERS = 32;
    constexpr unsigned N_ITERS = 20;
    constexpr auto BLOCK_DUR = std::chrono::milliseconds(200);
    constexpr auto WORKER_YIELD = std::chrono::microseconds(100);

    std::vector<int64_t> latencies;

    for (unsigned iter = 0; iter < N_ITERS; ++iter) {
        monad::fiber::PriorityPool pool(
            N_THREADS, N_FIBERS, /*prevent_spin=*/false);

        boost::fibers::promise<void> trigger;
        std::atomic<bool> ran{false};
        std::atomic<bool> stop{false};
        clock_type::time_point t_signal;
        clock_type::time_point t_run;

        // High-priority fiber: block on promise, record when it resumes
        pool.submit(0, [&] {
            trigger.get_future().wait();
            t_run = clock_type::now();
            ran.store(true, std::memory_order_release);
        });

        // 3 blockers: occupy 3 of 4 threads with long, non-yielding spin
        for (int i = 0; i < 3; ++i) {
            pool.submit(500, [&stop, BLOCK_DUR] {
                auto const deadline = clock_type::now() + BLOCK_DUR;
                while (clock_type::now() < deadline &&
                       !stop.load(std::memory_order_relaxed)) {
                }
            });
        }

        // Workers: yield frequently so pick_next() runs often
        for (unsigned i = 0; i < 20; ++i) {
            pool.submit(1000, [&stop, WORKER_YIELD] {
                while (!stop.load(std::memory_order_relaxed)) {
                    auto const d = clock_type::now() + WORKER_YIELD;
                    while (clock_type::now() < d) {
                    }
                    boost::this_fiber::yield();
                }
            });
        }

        // Let blockers occupy 3 threads and workers start on the 4th
        std::this_thread::sleep_for(std::chrono::milliseconds(50));

        // Signal from main thread -> cross-thread schedule_from_remote()
        t_signal = clock_type::now();
        trigger.set_value();

        // Wait with timeout
        auto const timeout = clock_type::now() + std::chrono::milliseconds(500);
        while (!ran.load(std::memory_order_acquire) &&
               clock_type::now() < timeout) {
            std::this_thread::sleep_for(std::chrono::microseconds(50));
        }

        stop.store(true, std::memory_order_release);

        latencies.push_back(
            ran.load() ? std::chrono::duration_cast<std::chrono::microseconds>(
                             t_run - t_signal)
                             .count()
                       : 500'000);
    }

    std::sort(latencies.begin(), latencies.end());
    auto const p75 = latencies[N_ITERS * 3 / 4];

    // With awakened_from_remote: p75 < 1ms (worker thread picks it up)
    // Without (old remote_ready_queue_): p75 >> 50ms (stuck behind blocker)
    EXPECT_LT(p75, 10'000);
}
