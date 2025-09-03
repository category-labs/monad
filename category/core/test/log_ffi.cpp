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

#include <category/core/log_ffi.h>

#include <bit>
#include <chrono>
#include <cstdint>
#include <print>
#include <string_view>
#include <thread>

#include <stdlib.h>
#include <string.h>

#include <gtest/gtest.h>
#include <quill/Quill.h>

static void capture_log(monad_log const *input_log, uintptr_t ptr)
{
    // The "logging" function makes a copy of the `monad_log` object, to be
    // tested after the logging completes; we also copy the message's string
    // buffer, since the logging framework may destroy it after this returns
    monad_log *const output_log = std::bit_cast<monad_log *>(ptr);
    *output_log = *input_log;
    if (output_log->message != nullptr) {
        output_log->message = strdup(output_log->message);
    }
}

TEST(LogFFI, Basic)
{
    constexpr uint8_t SYSLOG_ERR = 3;
    constexpr uint8_t SYSLOG_WARN = 4;
    monad_log_handler *handler;
    monad_log output = {};

    ASSERT_EQ(
        0,
        monad_log_handler_create(
            &handler,
            "test_handler",
            capture_log,
            nullptr,
            std::bit_cast<uintptr_t>(&output)));
    ASSERT_EQ(0, monad_log_init(&handler, 1, SYSLOG_WARN));

// A macro because it has to be literal, not even constexpr
#define FIRST_ERROR "First error"
    LOG_ERROR(FIRST_ERROR);

    // Give the quill background thread ample time to drain the log queue,
    // only then will the `capture_log` callback above be run; we wait a
    // whole second because the time to warm up this thread is quite long
    std::this_thread::sleep_for(std::chrono::seconds{1});

    EXPECT_EQ(SYSLOG_ERR, output.syslog_level);
    ASSERT_NE(nullptr, output.message);
    EXPECT_TRUE(strncmp(FIRST_ERROR, output.message, sizeof FIRST_ERROR));
    EXPECT_EQ(strlen(output.message), output.message_len);

    std::print(stderr, "First log message is: {}", output.message);
    free(const_cast<char *>(output.message));
    output = {};

#define SECOND_ERROR "Second error"
    LOG_ERROR(SECOND_ERROR);

    // Recording happens at much more interactive rates once the background
    // thread is warmed up; we make that thread aggressively sleep to avoid
    // wasting CPU resources, but even so this wait number _could_ be much
    // lower. We keep it unrealistically high so that the test won't fail
    // intermittently in the CI even when the system is under extreme
    // scheduling pressure
    std::this_thread::sleep_for(std::chrono::milliseconds{100});

    EXPECT_EQ(SYSLOG_ERR, output.syslog_level);
    ASSERT_NE(nullptr, output.message);
    EXPECT_TRUE(strncmp(SECOND_ERROR, output.message, sizeof SECOND_ERROR));
    EXPECT_EQ(strlen(output.message), output.message_len);

    std::print(stderr, "Second log message is: {}", output.message);
    free(const_cast<char *>(output.message));
    output = {};

    LOG_INFO("Hello, world");
    std::this_thread::sleep_for(std::chrono::milliseconds{100});

    // Because we initialized with SYSLOG_WARN, LOG_INFO won't do anything
    EXPECT_EQ(0, output.syslog_level);
    EXPECT_EQ(nullptr, output.message);
    EXPECT_EQ(0, output.message_len);
}
