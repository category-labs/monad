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

#include <category/core/io/ring.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <liburing.h>
#include <liburing/io_uring.h>

#include <chrono>
#include <optional>
#include <string_view>
#include <thread>

using namespace monad::io;

namespace
{
    // An SQPOLL ring's fdinfo as Linux 7.0 prints it.
    constexpr std::string_view SQPOLL_RING_FDINFO = "pos:\t0\n"
                                                    "flags:\t02000002\n"
                                                    "mnt_id:\t16\n"
                                                    "ino:\t3636802\n"
                                                    "SqMask:\t0x7f\n"
                                                    "SqHead:\t2\n"
                                                    "SqTail:\t2\n"
                                                    "CachedSqHead:\t2\n"
                                                    "CqMask:\t0xff\n"
                                                    "CqHead:\t2\n"
                                                    "CqTail:\t2\n"
                                                    "CachedCqTail:\t2\n"
                                                    "SQEs:\t0\n"
                                                    "CQEs:\t0\n"
                                                    "SqThread:\t1419206\n"
                                                    "SqThreadCpu:\t127\n"
                                                    "SqTotalTime:\t4194063\n"
                                                    "SqWorkTime:\t1234\n"
                                                    "UserFiles:\t1\n"
                                                    "UserBufs:\t1\n"
                                                    "PollList:\n"
                                                    "CqOverflowList:\n"
                                                    "NAPI:\tdisabled\n";

    // What Linux 6.15 and later print when the SQPOLL thread held the lock.
    constexpr std::string_view LOCK_MISSED_FDINFO = "pos:\t0\n"
                                                    "flags:\t02000002\n"
                                                    "mnt_id:\t16\n"
                                                    "ino:\t3636802\n";

    // What Linux 6.9 to 6.14 print then, following io_uring/fdinfo.c.
    constexpr std::string_view LOCK_MISSED_BEFORE_6_15_FDINFO =
        "pos:\t0\n"
        "flags:\t02000002\n"
        "mnt_id:\t16\n"
        "ino:\t3636802\n"
        "SqMask:\t0x7f\n"
        "SqHead:\t2\n"
        "SqTail:\t2\n"
        "CachedSqHead:\t2\n"
        "CqMask:\t0xff\n"
        "CqHead:\t2\n"
        "CqTail:\t2\n"
        "CachedCqTail:\t2\n"
        "SQEs:\t0\n"
        "CQEs:\t0\n"
        "SqThread:\t-1\n"
        "SqThreadCpu:\t-1\n"
        "SqTotalTime:\t0\n"
        "SqWorkTime:\t0\n"
        "UserFiles:\t1\n"
        "UserBufs:\t1\n"
        "PollList:\n"
        "CqOverflowList:\n"
        "NAPI:\tdisabled\n";

    // What Linux 6.8 prints with the lock: the thread, but not its times.
    constexpr std::string_view BEFORE_6_9_FDINFO = "SqMask:\t0x7f\n"
                                                   "SqThread:\t1419206\n"
                                                   "SqThreadCpu:\t127\n"
                                                   "UserFiles:\t1\n";

    std::optional<SqPollTimesUnavailable>
    unavailable(std::string_view const fdinfo)
    {
        auto const times = parse_sqpoll_times(fdinfo);
        if (times.has_value()) {
            return std::nullopt;
        }
        return times.error();
    }
}

TEST(ParseSqPollTimes, reads_both_times_in_nanoseconds)
{
    auto const times = parse_sqpoll_times(SQPOLL_RING_FDINFO);
    ASSERT_TRUE(times.has_value());
    EXPECT_EQ(times->total_ns, 4'194'063'000u);
    EXPECT_EQ(times->work_ns, 1'234'000u);
}

TEST(ParseSqPollTimes, a_read_that_lost_the_lock_is_contended)
{
    EXPECT_EQ(
        unavailable(LOCK_MISSED_FDINFO), SqPollTimesUnavailable::contended);
    EXPECT_EQ(
        unavailable(LOCK_MISSED_BEFORE_6_15_FDINFO),
        SqPollTimesUnavailable::contended);
}

TEST(ParseSqPollTimes, a_kernel_showing_the_thread_without_times_is_unsupported)
{
    EXPECT_EQ(
        unavailable(BEFORE_6_9_FDINFO), SqPollTimesUnavailable::unsupported);
    EXPECT_EQ(
        unavailable("SqThread:\t7\nSqTotalTime:\t5\n"),
        SqPollTimesUnavailable::unsupported);
    EXPECT_EQ(
        unavailable("SqThread:\t7\nSqWorkTime:\t5\n"),
        SqPollTimesUnavailable::unsupported);
}

TEST(ParseSqPollTimes, rejects_a_malformed_value)
{
    EXPECT_EQ(
        unavailable("SqThread:\t7\nSqTotalTime:\t5x\nSqWorkTime:\t1\n"),
        SqPollTimesUnavailable::unsupported);
    EXPECT_EQ(
        unavailable("SqThread:\t7\nSqTotalTime:\t\nSqWorkTime:\t1\n"),
        SqPollTimesUnavailable::unsupported);
}

TEST(Ring, has_no_sqpoll_times_without_sqpoll)
{
    Ring const ring{RingConfig{8}};
    auto const times = ring.sqpoll_times();
    ASSERT_FALSE(times.has_value());
    EXPECT_EQ(times.error(), SqPollTimesUnavailable::no_sqpoll);
}

TEST(Ring, reads_its_sqpoll_thread_times)
{
    Ring ring{RingConfig{8, 0}};
    // A new SQPOLL thread sleeps until a first submission wakes it, and only
    // then spins for its idle timeout.
    io_uring_sqe *const sqe = io_uring_get_sqe(&ring.get_ring());
    ASSERT_NE(sqe, nullptr);
    io_uring_prep_nop(sqe);
    ASSERT_EQ(io_uring_submit(&ring.get_ring()), 1);
    io_uring_cqe *cqe{nullptr};
    ASSERT_EQ(io_uring_wait_cqe(&ring.get_ring(), &cqe), 0);
    io_uring_cqe_seen(&ring.get_ring(), cqe);

    auto const first = ring.sqpoll_times();
    if (!first.has_value() &&
        first.error() == SqPollTimesUnavailable::unsupported) {
        GTEST_SKIP() << "kernel does not report SQPOLL thread times";
    }
    ASSERT_TRUE(first.has_value());
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    auto const second = ring.sqpoll_times();
    ASSERT_TRUE(second.has_value());
    EXPECT_GT(second->total_ns, first->total_ns);
    EXPECT_GE(second->work_ns, first->work_ns);
    EXPECT_LE(second->work_ns, second->total_ns);
}
