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

#include <gtest/gtest.h>

#include <category/core/fiber/priority_pool.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <atomic>
#include <chrono>
#include <cstddef>
#include <functional>
#include <iostream>
#include <thread>
#include <vector>

/* On Niall's machine, for reference:

PriorityPool executed 700000 ops which is 126020 ops/sec.

For comparison, a single CPU core can execute 2673500000 ops which
is 5.34684e+08 ops/sec.

This makes PriorityPool 0.000235691 times faster than a single CPU core.
Hardware concurrency is 64
*/

TEST(PriorityPool, benchmark)
{
    monad::fiber::PriorityPool ppool(
        (unsigned)std::thread::hardware_concurrency(),
        (unsigned)std::thread::hardware_concurrency() * 4);

    struct count_t
    {
        alignas(64) std::atomic<unsigned> count{0};
        std::byte padding_[56];
        count_t() = default;

        count_t(count_t const &) {}
    };

    static_assert(sizeof(count_t) == 64);

    std::vector<count_t> counts(std::thread::hardware_concurrency());
    std::atomic<size_t> countsidx{0};
    std::function<void()> const task([&] {
        static thread_local size_t const mycountidx =
            countsidx.fetch_add(1, std::memory_order_acq_rel);
        counts[mycountidx].count.fetch_add(1, std::memory_order_acq_rel);
    });
    auto sum = [&] {
        unsigned ret = 0;
        for (auto const &i : counts) {
            ret += i.count.load(std::memory_order_acquire);
        }
        return ret;
    };
    auto begin = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(1)) {
        ;
    }

    unsigned submitted = 0;
    begin = std::chrono::steady_clock::now();
    auto end = begin;
    for (;;) {
        for (size_t n = 0; n < 100000; n++) {
            ppool.submit(1, task);
        }
        submitted += 100000;
        end = std::chrono::steady_clock::now();
        if (end - begin >= std::chrono::seconds(5)) {
            break;
        }
    }
    while (sum() < submitted) {
        std::this_thread::yield();
    }
    end = std::chrono::steady_clock::now();
    double const ops_per_sec1 =
        1000000000.0 * double(submitted) /
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    std::cout << "PriorityPool executed " << submitted << " ops which is "
              << ops_per_sec1 << " ops/sec." << std::endl;

    for (auto &i : counts) {
        EXPECT_GT(i.count.load(std::memory_order_acquire), 0);
        i.count.store(0, std::memory_order_release);
    }
    counts.resize(counts.size() + 1);
    begin = std::chrono::steady_clock::now();
    for (;;) {
        for (size_t n = 0; n < 100000; n++) {
            task();
        }
        end = std::chrono::steady_clock::now();
        if (end - begin >= std::chrono::seconds(5)) {
            break;
        }
    }
    auto const count = sum();
    double const ops_per_sec2 =
        1000000000.0 * double(count) /
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    std::cout << "\nFor comparison, a single CPU core can execute " << count
              << " ops which is " << ops_per_sec2 << " ops/sec.\n";
    std::cout
        << "\nThis makes PriorityPool " << (ops_per_sec1 / ops_per_sec2)
        << " times faster than a single CPU core. Hardware concurrency is "
        << std::thread::hardware_concurrency() << std::endl;
}
