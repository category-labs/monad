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

#include <category/core/terminate_handler.h>

#include <gtest/gtest.h>

#include <exception>
#include <stdexcept>

namespace
{

    void throwing_function()
    {
        throw std::runtime_error("Test exception from throwing_function");
    }

    // NOLINTNEXTLINE(bugprone-exception-escape)
    void noexcept_function() noexcept
    {
        // This will call std::terminate because we're throwing from noexcept
        throwing_function();
    }

} // namespace

// Death tests must be named with DeathTest suffix for proper test ordering
TEST(TerminateHandlerDeathTest, ExceptionEscapingNoexcept)
{
    // Install the custom terminate handler
    monad_set_terminate_handler();

    // Verify that calling noexcept_function causes termination
    // and that the output contains expected exception information
    EXPECT_DEATH(
        { noexcept_function(); },
        // Regex pattern matching expected output:
        // - Should contain "std::terminate" or "terminate()"
        // - Should contain the exception type "runtime_error"
        // - Should contain the exception message
        // - Should contain "Stack trace"
        "std::terminate.*"
        ".*runtime_error.*"
        ".*Test exception from throwing_function.*"
        ".*Stack trace.*");
}

TEST(TerminateHandlerDeathTest, DirectTerminateCall)
{
    // Install the custom terminate handler
    monad_set_terminate_handler();

    // Verify that directly calling std::terminate works
    EXPECT_DEATH(
        { std::terminate(); },
        // Should indicate no active exception
        "std::terminate.*"
        ".*No active exception detected.*"
        ".*Stack trace.*");
}

#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wexceptions"
#else
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wterminate"
#endif

// Helper function for testing different exception type
// NOLINTNEXTLINE(bugprone-exception-escape)
[[noreturn]] void throw_logic_error_noexcept() noexcept
{
    throw std::logic_error("Logic error test");
}

#ifdef __clang__
    #pragma clang diagnostic pop
#else
    #pragma GCC diagnostic pop
#endif

TEST(TerminateHandlerDeathTest, ExceptionTypeInOutput)
{
    // Install the custom terminate handler
    monad_set_terminate_handler();

    // Test with a different exception type
    EXPECT_DEATH(
        { throw_logic_error_noexcept(); },
        "std::terminate.*"
        ".*logic_error.*"
        ".*Logic error test.*");
}
