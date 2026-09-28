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

#include <category/core/log.hpp>
#include <category/core/log_ffi.h>

#include <cstdint>
#include <print>
#include <string>

#include <gtest/gtest.h>

struct CapturedLog
{
    uint8_t syslog_level;
    std::string message;
};

static void capture_log(monad_log const *const input_log, uintptr_t const ptr)
{
    // The "logging" function makes a copy of the `monad_log` object, to be
    // tested after the logging completes; we also copy the message's string
    // buffer, since the logging framework may destroy it after this returns
    CapturedLog *const output_log = reinterpret_cast<CapturedLog *>(ptr);
    output_log->syslog_level = input_log->syslog_level;
    output_log->message.assign(input_log->message, input_log->message_len);
}

TEST(LogFFI, Basic)
{
    constexpr uint8_t SYSLOG_ERR = 3;
    constexpr uint8_t SYSLOG_WARN = 4;
    monad_log_handler *handler;
    CapturedLog output = {};

    ASSERT_EQ(
        0,
        monad_log_handler_create(
            &handler,
            "test_handler",
            capture_log,
            nullptr,
            reinterpret_cast<uintptr_t>(&output)));
    ASSERT_EQ(0, monad_log_init(&handler, 1, SYSLOG_WARN));

// A macro because it has to be literal, not even constexpr
#define FIRST_ERROR "First error"
    LOG_ERROR(FIRST_ERROR);
    monad::flush_logger();

    EXPECT_EQ(SYSLOG_ERR, output.syslog_level);
    EXPECT_TRUE(output.message.ends_with(FIRST_ERROR "\n"));

    std::print(stderr, "First log message is: {}", output.message);
    output = {};

#define SECOND_ERROR "Second error"
    LOG_ERROR(SECOND_ERROR);
    monad::flush_logger();

    EXPECT_EQ(SYSLOG_ERR, output.syslog_level);
    EXPECT_TRUE(output.message.ends_with(SECOND_ERROR "\n"));

    std::print(stderr, "Second log message is: {}", output.message);
    output = {};

    LOG_INFO("Hello, world");
    monad::flush_logger();

    // Because we initialized with SYSLOG_WARN, LOG_INFO won't do anything
    EXPECT_EQ(0, output.syslog_level);
    EXPECT_TRUE(output.message.empty());

    monad_log_handler_destroy(handler);
}
