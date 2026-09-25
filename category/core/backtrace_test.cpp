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
#include <cstdio>
#include <cstring>
#include <span>
#include <vector>

#include <gtest/gtest.h>

#include <bits/time.h>
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

    __attribute__((noinline)) void capture_at_depth(
        unsigned const depth, std::span<std::byte> const storage,
        monad::stack_backtrace::ptr &out)
    {
        if (depth == 0) {
            out = monad::stack_backtrace::capture(storage);
            return;
        }
        capture_at_depth(depth - 1, storage, out);
        asm volatile("" ::: "memory"); // keep the call out of tail position
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

    TEST(BacktraceTest, deep_stack_stays_in_storage)
    {
        constexpr size_t storage_size = 16384;
        constexpr std::byte guard{0xa5};
        std::vector<std::byte> memory(5 * storage_size, guard);
        std::span<std::byte> const all{memory};
        monad::stack_backtrace::ptr st;
        capture_at_depth(2000, all.first(storage_size), st);
        EXPECT_TRUE(std::ranges::all_of(
            all.subspan(storage_size), [](std::byte b) { return b == guard; }));

        int fds[2];
        ASSERT_EQ(0, ::pipe(fds));
        st->print(fds[1], 0, false);
        ::close(fds[1]);
        char out[64];
        auto const n = ::read(fds[0], out, sizeof(out));
        ::close(fds[0]);
        ASSERT_EQ(1, n);
        EXPECT_EQ('\n', out[0]);
    }
}
