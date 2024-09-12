#include <monad/core/backtrace.hpp>

#include <monad/core/assert.h>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <array>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <span>

#include <time.h>
#include <unistd.h>

namespace
{
    __attribute__((noinline)) monad::stack_backtrace::ptr
    func_b(std::span<std::byte> storage)
    {
        return monad::stack_backtrace::capture(storage);
    }

    __attribute__((noinline)) monad::stack_backtrace::ptr
    func_a(std::span<std::byte> storage)
    {
        return func_b(storage);
    }

    TEST(BacktraceTest, works)
    {
        std::array<std::byte, 1024> storage;
        auto st = func_a(storage);
        int fds[2];
        timespec resolution;
        MONAD_ASSERT(-1 != ::pipe(fds));
        MONAD_ASSERT(
            -1 != clock_getres(CLOCK_REALTIME, &resolution),
            "clock_getres(3) failed for clock %d",
            CLOCK_REALTIME);

        struct unfds_t
        {
            int *fds;

            explicit unfds_t(int *fds_)
                : fds(fds_)
            {
            }

            ~unfds_t()
            {
                ::close(fds[0]);
                ::close(fds[1]);
            }
        } unfds{fds};

        st->print(fds[1], 3, true);
        char buffer[16384];
        auto bytesread = ::read(fds[0], buffer, sizeof(buffer));
        buffer[bytesread] = 0;
        puts("Backtrace was:");
        puts(buffer);
        EXPECT_NE(nullptr, strstr(buffer, "func_a"));
        EXPECT_NE(nullptr, strstr(buffer, "func_b"));
        EXPECT_NE(nullptr, strstr(buffer, "/test/backtrace.cpp"));
    }
}
