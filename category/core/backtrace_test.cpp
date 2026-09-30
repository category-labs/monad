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

#include <category/core/assert.h>
#include <category/core/backtrace.hpp>

#include <category/core/assert.h>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <span>
#include <string>

#include <gtest/gtest.h>

#include <bits/time.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

namespace
{
    __attribute__((noinline)) monad::stack_backtrace::ptr
    func_b(std::span<std::byte> const storage)
    {
        return monad::stack_backtrace::capture(storage);
    }

    __attribute__((noinline)) monad::stack_backtrace::ptr
    func_a(std::span<std::byte> const storage)
    {
        return func_b(storage);
    }

    __attribute__((noinline)) monad::stack_backtrace::ptr
    capture_deep(std::span<std::byte> const storage, unsigned const depth)
    {
        if (depth == 0) {
            return func_a(storage);
        }
        auto trace = capture_deep(storage, depth - 1);
        // Keep the recursive frames present in optimized builds.
        asm volatile("" : : "r"(depth) : "memory");
        return trace;
    }

    std::string
    print_trace(monad::stack_backtrace const &trace, bool const symbolize)
    {
        auto const close_file = [](FILE *const file) { std::fclose(file); };
        std::unique_ptr<FILE, decltype(close_file)> const output{
            std::tmpfile(), close_file};
        EXPECT_NE(output, nullptr);
        if (!output) {
            return {};
        }
        trace.print(fileno(output.get()), 0, symbolize);
        EXPECT_EQ(std::fseek(output.get(), 0, SEEK_SET), 0);
        std::string result;
        char line[1024];
        while (std::fgets(line, sizeof(line), output.get())) {
            result += line;
        }
        EXPECT_EQ(std::ferror(output.get()), 0);
        return result;
    }

    TEST(BacktraceTest, unaligned_storage)
    {
        alignas(64) std::array<std::byte, 16384 + 64> storage;
        for (size_t offset = 0; offset < 64; ++offset) {
            SCOPED_TRACE(offset);
            auto const trace =
                func_a(std::span{storage}.subspan(offset, 16384));
            ASSERT_NE(trace, nullptr);
            EXPECT_EQ(
                reinterpret_cast<uintptr_t>(trace.get()) %
                    alignof(monad::stack_backtrace),
                0);
        }
    }

    TEST(BacktraceTest, deep_unaligned_storage)
    {
        alignas(64) std::array<std::byte, 16384 + 1> storage;
        auto const trace = capture_deep(std::span{storage}.subspan(1), 160);
        ASSERT_NE(trace, nullptr);
        auto const output = print_trace(*trace, false);
        EXPECT_GT(std::count(output.begin(), output.end(), '\n') - 1, 128);
    }

    TEST(BacktraceDeathTest, empty_storage)
    {
        EXPECT_DEATH(monad::stack_backtrace::capture({}), "");
    }

    TEST(BacktraceDeathTest, insufficient_storage)
    {
        std::array<std::byte, 1> storage;
        EXPECT_DEATH(monad::stack_backtrace::capture(storage), "");
    }

    TEST(BacktraceTest, truncated_stack_preserves_innermost_frames)
    {
        for (unsigned const depth : {32u, 160u}) {
            SCOPED_TRACE(depth);
            alignas(64) std::array<std::byte, 256 + 64> storage;
            storage.fill(std::byte{0x5a});
            auto const trace =
                capture_deep(std::span{storage}.subspan(1, 256), depth);
            ASSERT_NE(trace, nullptr);

            auto const output = print_trace(*trace, false);
            auto const frame_count =
                std::count(output.begin(), output.end(), '\n') - 1;
            EXPECT_GT(frame_count, 0);
            EXPECT_LT(frame_count, depth);

            auto const symbols = print_trace(*trace, true);
            EXPECT_NE(symbols.find("func_a"), std::string::npos);
            EXPECT_NE(symbols.find("func_b"), std::string::npos);
            EXPECT_EQ(symbols.find("TestBody"), std::string::npos);

            EXPECT_EQ(storage.front(), std::byte{0x5a});
            for (size_t i = 257; i < storage.size(); ++i) {
                EXPECT_EQ(storage[i], std::byte{0x5a});
            }
        }
    }

    TEST(BacktraceTest, works)
    {
        std::array<std::byte, 1024> storage;
        auto st = func_a(storage);
        int fds[2];
        timespec resolution;
        [[maybe_unused]] char const *i_am_null = nullptr;
        MONAD_ASSERT(-1 != ::pipe(fds));
        MONAD_ASSERT(true, "most definitely true!");

        /*
         * If you uncomment the MONAD_{ASSERT,ABORT} below, it will not compile,
         * because `i_am_null` is not a compile-time constant. The intention is
         * to make it fail unless a fixed-address string is provided. Note that
         * if we wrote `char const *const i_am_null = nullptr` instead, it would
         * succeed since __builtin_constant_p(i_am_null) is true. That is OK
         * (nullptr is explicitly checked for); all we're trying to prevent here
         * here is dereferencing runtime-dynamic invalid pointers during assert
         * failure handling. A known compile-time constant `char const *` value
         * should either be nullptr or is almost certainly safe to dereference.
         */
        // MONAD_ASSERT(true, i_am_null);
        // MONAD_ABORT(i_am_null);

        MONAD_ASSERT_PRINTF(
            -1 != clock_getres(CLOCK_REALTIME, &resolution),
            "clock_getres(3) failed for clock %d",
            CLOCK_REALTIME);

        struct unfds_t
        {
            int *fds;

            explicit unfds_t(int *const fds_)
                : fds(fds_)
            {
            }

            ~unfds_t()
            {
                ::close(fds[0]);
                ::close(fds[1]);
            }
        } const unfds{fds};

        st->print(fds[1], 3, true);
        char buffer[16384];
        auto const bytesread = ::read(fds[0], buffer, sizeof(buffer));
        buffer[bytesread] = 0;
        puts("Backtrace was:");
        puts(buffer);
        EXPECT_NE(nullptr, strstr(buffer, "func_a"));
        EXPECT_NE(nullptr, strstr(buffer, "func_b"));
        EXPECT_NE(nullptr, strstr(buffer, "/backtrace_test.cpp"));
    }
}
