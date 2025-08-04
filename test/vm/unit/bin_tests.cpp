#include <category/vm/runtime/bin.hpp>

#include <gtest/gtest.h>

using namespace monad::vm::runtime;

namespace
{
    // bin_construction_test<0>
    // ...
    // bin_construction_test<32>
    template <size_t N>
    void bin_construction_test()
    {
        constexpr auto upper = Bin<N>::upper;
        Bin<N> b;
        ASSERT_EQ(*b, 0);
        b = bin<upper>;
        ASSERT_EQ(*b, upper);
        Bin<N> c{b};
        ASSERT_EQ(*c, upper);
        Bin<N> d{Bin<N>::unsafe_from(upper)};
        ASSERT_EQ(*d, upper);
        if constexpr (N < 32) {
            bin_construction_test<N + 1>();
        }
    }

    // bin_add_test<0, 0>
    // bin_add_test<1, 0>
    // ...
    // bin_add_test<31, 0>
    // bin_add_test<63, 0>
    // bin_add_test<0, 1>
    // ...
    // bin_add_test<63, 1>
    // bin_add_test<0, 3>
    // ...
    // bin_add_test<63, 3>
    // ...
    template <size_t M, size_t N>
    void bin_add_test()
    {
        constexpr auto R = std::max(M, N) + 1;
        if constexpr (R <= 32) {
            auto const left = bin<Bin<M>::upper>;
            auto const right = bin<Bin<N>::upper>;
            auto const expected = uint64_t{*left} + uint64_t{*right};
            auto const actual = left + right;

            static_assert(sizeof(uint64_t) > sizeof(left));
            static_assert(sizeof(uint64_t) > sizeof(right));
            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
        if constexpr (M < 32) {
            bin_add_test<M + M + 1, N>();
        }
        else if constexpr (N < 32) {
            bin_add_test<0, N + N + 1>();
        }
    }

    // bin_mul_test<0, 0>
    // ...
    // bin_mul_test<32, 0>
    // bin_mul_test<0, 8>
    // ...
    // bin_mul_test<32, 8>
    // ...
    template <size_t M, size_t N>
    void bin_mul_test()
    {
        constexpr auto R = M + N;
        if constexpr (R <= 32) {
            auto const left = bin<Bin<M>::upper>;
            auto const right = bin<Bin<N>::upper>;
            auto const expected = uint64_t{*left} * uint64_t{*right};
            auto const actual = left * right;

            static_assert(sizeof(uint64_t) > sizeof(left));
            static_assert(sizeof(uint64_t) > sizeof(right));
            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
        if constexpr (M < 32) {
            bin_mul_test<M + 8, N>();
        }
        else if constexpr (N < 32) {
            bin_mul_test<0, N + 8>();
        }
    }

    // bin_shr_test<0, 0>
    // bin_shr_test<1, 0>
    // ...
    // bin_shr_test<31, 0>
    // bin_shr_test<63, 0>
    // bin_shr_test<0, 8>
    // ...
    // bin_shr_test<63, 8>
    // bin_shr_test<0, 16>
    // ...
    // bin_shr_test<63, 16>
    // ...
    template <size_t x, size_t N>
    void bin_shr_test()
    {
        constexpr auto R = N - x;

        if constexpr (x < 32 && N <= 32 && R <= 32) {
            auto const value = bin<Bin<N>::upper>;
            auto const expected = uint64_t{*value} / (uint64_t{1} << x);
            auto const actual = shr<x>(value);

            static_assert(sizeof(uint64_t) > sizeof(value));
            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
        if constexpr (x < 32) {
            bin_shr_test<x + x + 1, N>();
        }
        else if constexpr (N < 32) {
            bin_shr_test<0, N + 8>();
        }
    }

    // bin_shl_test<0, 0>
    // bin_shl_test<1, 0>
    // ...
    // bin_shl_test<31, 0>
    // bin_shl_test<63, 0>
    // bin_shl_test<0, 8>
    // ...
    // bin_shl_test<63, 8>
    // bin_shl_test<0, 16>
    // ...
    // bin_shl_test<63, 16>
    // ...
    template <size_t x, size_t N>
    void bin_shl_test()
    {
        constexpr auto R = N + x;

        if constexpr (x < 32 && R <= 32) {
            auto const value = bin<Bin<N>::upper>;
            auto const expected = uint64_t{*value} * (uint64_t{1} << x);
            auto const actual = shl<x>(value);

            static_assert(sizeof(uint64_t) > sizeof(value));
            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
        if constexpr (x < 32) {
            bin_shl_test<x + x + 1, N>();
        }
        else if constexpr (N < 32) {
            bin_shl_test<0, N + 8>();
        }
    }

    template <uint32_t x, size_t N, uint32_t v>
    void bin_shr_ceil_assert()
    {
        constexpr auto R = std::max(size_t{x}, N) - x + 1;
        if constexpr (R <= 32) {
            Bin<N> const value = bin<v>;
            auto const expected = uint64_t{*value / (uint64_t{1} << x)} +
                                  uint64_t{*value % (uint64_t{1} << x) != 0};

            auto const actual = shr_ceil<x>(value);

            static_assert(sizeof(uint64_t) > sizeof(value));
            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
    }

    // bin_shr_ceil_test<0, 0>
    // bin_shr_ceil_test<1, 0>
    // ...
    // bin_shr_ceil_test<31, 0>
    // bin_shr_ceil_test<63, 0>
    // bin_shr_ceil_test<0, 1>
    // ...
    // bin_shr_ceil_test<63, 1>
    // bin_shr_ceil_test<0, 3>
    // ...
    // bin_shr_ceil_test<63, 3>
    // ...
    template <uint32_t x, size_t N>
    void bin_shr_ceil_test()
    {
        if constexpr (x < 32 && N < 32) {
            constexpr auto bound = std::min(Bin<N>::upper, Bin<x>::upper);
            bin_shr_ceil_assert<x, N, Bin<N>::upper - bound>();
            bin_shr_ceil_assert<x, N, Bin<N>::upper - bound / 2>();
            bin_shr_ceil_assert<x, N, Bin<N>::upper>();
        }
        if constexpr (x < 32) {
            bin_shr_ceil_test<x + x + 1, N>();
        }
        else if constexpr (N < 32) {
            bin_shr_ceil_test<0, N + N + 1>();
        }
    }

    // bin_max_test<0, 0>
    // ...
    // bin_max_test<32, 0>
    // bin_max_test<0, 8>
    // ...
    // bin_max_test<32, 8>
    // ...
    template <size_t M, size_t N>
    void bin_max_test()
    {
        constexpr auto R = std::max(M, N);
        if constexpr (R <= 32) {
            auto const left = bin<Bin<M>::upper>;
            auto const right = bin<Bin<N>::upper>;
            auto const expected = std::max(*left, *right);
            auto const actual = max(left, right);

            static_assert(std::is_same_v<decltype(actual), Bin<R> const>);
            ASSERT_EQ(*actual, expected);
            ASSERT_LE(expected, Bin<R>::upper);
        }
        if constexpr (M < 32) {
            bin_max_test<M + 8, N>();
        }
        else if constexpr (N < 32) {
            bin_max_test<0, N + 8>();
        }
    }
}

TEST(Bin, construction)
{
    bin_construction_test<0>();
}

TEST(Bin, add)
{
    bin_add_test<0, 0>();
}

TEST(Bin, mul)
{
    bin_mul_test<0, 0>();
}

TEST(Bin, shr)
{
    bin_shr_test<0, 0>();
}

TEST(Bin, shl)
{
    bin_shl_test<0, 0>();
}

TEST(Bin, shr_ceil)
{
    bin_shr_ceil_test<0, 0>();
}

TEST(Bin, max)
{
    bin_max_test<0, 0>();
}
