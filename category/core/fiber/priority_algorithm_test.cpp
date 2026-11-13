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

#include <category/core/fiber/priority_algorithm.hpp>
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_queue.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/channel_op_status.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <cstdint>
#include <latch>
#include <thread>
#include <vector>

TEST(PriorityAlgorithm, remote_wakes_run_elsewhere_in_priority_order)
{
    using monad::fiber::PriorityProperties;
    monad::fiber::PriorityQueue queue;
    boost::fibers::buffered_channel<int> urgent_channel{2};
    boost::fibers::buffered_channel<int> other_channel{2};
    boost::fibers::buffered_channel<int> middle_channel{2};
    std::latch waiting{1};
    std::latch other_queued{1};
    std::latch urgent_queued{1};
    std::latch owner_blocked{1};
    std::latch release_owner{1};
    std::vector<int> order;

    std::thread owner([&] {
        boost::fibers::use_scheduling_algorithm<
            monad::fiber::PriorityAlgorithm>(queue);
        auto wait = [&](auto &channel, uint64_t priority) {
            boost::this_fiber::properties<PriorityProperties>().set_priority(
                priority);
            int id = 0;
            EXPECT_EQ(
                channel.pop(id), boost::fibers::channel_op_status::success);
            order.push_back(id);
        };
        boost::fibers::fiber urgent([&] { wait(urgent_channel, 1); });
        boost::fibers::fiber other([&] { wait(other_channel, 10); });
        boost::fibers::fiber middle([&] { wait(middle_channel, 5); });
        boost::this_fiber::yield(); // all three workers block before main
        waiting.count_down();

        other_queued.wait();
        urgent_queued.wait();
        EXPECT_EQ(
            middle_channel.push(2), boost::fibers::channel_op_status::success);
        owner_blocked.count_down();
        release_owner.wait();
        urgent.join();
        other.join();
        middle.join();
    });

    waiting.wait();
    EXPECT_EQ(other_channel.push(3), boost::fibers::channel_op_status::success);
    other_queued.count_down();
    EXPECT_EQ(
        urgent_channel.push(1), boost::fibers::channel_op_status::success);
    urgent_queued.count_down();
    owner_blocked.wait();
    std::thread helper([&] {
        boost::fibers::use_scheduling_algorithm<
            monad::fiber::PriorityAlgorithm>(queue);
        boost::this_fiber::yield();
    });
    helper.join();
    EXPECT_EQ(order, (std::vector<int>{1, 2, 3}));
    release_owner.count_down();
    owner.join();
}
