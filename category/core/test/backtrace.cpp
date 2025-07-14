#include <monad/core/assert.h>
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
