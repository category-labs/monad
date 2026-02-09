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

#include <category/async/uring_fiber_scheduler.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::fiber;

TEST(UringFiberSchedulerBasicTest, completion_token_magic)
{
    CompletionToken token;
    EXPECT_EQ(token.magic, CompletionToken::FIBER_COMPLETION_MAGIC);
    EXPECT_EQ(token.waiting_fiber, nullptr);
    EXPECT_EQ(token.result, 0);
    EXPECT_FALSE(token.completed);
}

TEST(UringFiberSchedulerBasicTest, completion_token_not_match_sender_receiver)
{
    // The first bytes of erased_connected_operation should NOT match the magic
    // number. erased_connected_operation starts with operation_type (0-3),
    // bool, bool, io_priority (0-2), then padding/pointer.
    // Our magic 0x4649424552434F4D (little-endian: 4D 4F 43 52 45 42 49 46)
    // starts with 0x4D which is not in range 0-3.

    std::array<uint8_t, 8> simulated_erased_op = {
        0x01, // operation_type::read
        0x00, // being_executed_ = false
        0x01, // lifetime_managed_internally_ = true
        0x00, // io_priority::highest
        0x00,
        0x00,
        0x00,
        0x00 // padding
    };

    uint64_t as_magic;
    std::memcpy(&as_magic, simulated_erased_op.data(), sizeof(as_magic));

    EXPECT_NE(as_magic, CompletionToken::FIBER_COMPLETION_MAGIC);
}
