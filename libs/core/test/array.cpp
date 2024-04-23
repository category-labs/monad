#include <monad/core/array.hpp>

#include <monad/config.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp>  // NOLINT

#include <gtest/gtest.h>

#include <utility>

namespace
{
    TEST(ArrayTest, make_array_of_immovable)
    {
        struct Foo
        {
            int x;
            Foo(int a, int b)
                : x(a + b)
            {
            }
            Foo(Foo const &) = delete;
            Foo(Foo &&) = delete;
            Foo &operator=(Foo const &) = delete;
            Foo &operator=(Foo &&) = delete;
        };
        auto arr =
            MONAD_NAMESPACE::make_array<Foo, 5>(std::piecewise_construct, 2, 3);
        EXPECT_EQ(arr.size(), 5);
        EXPECT_EQ(arr[0].x, 5);
        EXPECT_EQ(arr[1].x, 5);
        EXPECT_EQ(arr[2].x, 5);
        EXPECT_EQ(arr[3].x, 5);
        EXPECT_EQ(arr[4].x, 5);
    }
}
