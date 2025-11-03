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

#include <category/core/unordered_map.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>

#ifdef NDEBUG
    #include <category/core/small_prng.hpp>

    #include <chrono>
    #include <iostream>
    #include <unordered_set>
    #include <vector>
#endif

TEST(UnorderedNodeMap, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_node_map<int, int> map;
    map[5] = 6;
    EXPECT_EQ(map[5], 6);
}

TEST(UnorderedDenseMap, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_dense_map<int, int> map;
    map[5] = 6;
    EXPECT_EQ(map[5], 6);
}

TEST(UnorderedNodeSet, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_node_set<int> set;
    set.insert(5);
    EXPECT_TRUE(set.contains(5));
}

TEST(UnorderedDenseSet, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_dense_set<int> set;
    set.insert(5);
    EXPECT_TRUE(set.contains(5));
}

template <size_t count>
struct bytes
{
    char v[count]{};

    bytes(uint32_t x) // NOLINT
    {
        memcpy(v, &x, sizeof(x));
    }

    bool operator==(bytes const &o) const noexcept
    {
        return 0 == memcmp(v, o.v, count);
    }
};

struct hasher
{
    template <class T>
    size_t operator()(T const &v) const noexcept
    {
        return MONAD_NAMESPACE::hash_bytes(v.v, sizeof(v.v));
    }
};

template <class T>
struct tag
{
    using type = T;
};

TEST(UnorderedSets, DISABLED_quick_comparative_benchmark)
{
#ifdef NDEBUG
    using namespace MONAD_NAMESPACE;
    std::vector<uint32_t> values(5000000);
    small_prng rand;
    for (auto &i : values) {
        i = rand();
    }
    auto do_test = [&](auto tag1, char const *desc) {
        using T = typename decltype(tag1)::type;
        auto do_cont = [&](auto tag2, char const *desc2) {
            using cont = typename decltype(tag2)::type;
            std::cout << "   Testing " << desc2 << " with " << desc << " ... "
                      << std::flush;
            auto const begin = std::chrono::steady_clock::now();
            {
                cont c;
                for (auto const i : values) {
                    c.insert(i);
                }
                for (size_t n = 0; n < 10; n++) {
                    for (auto const i : values) {
                        auto const volatile it = c.find(i);
                        (void)it;
                    }
                }
            }
            auto const end = std::chrono::steady_clock::now();
            auto const diff =
                static_cast<double>(
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end - begin)
                        .count()) /
                1000000.0;
            std::cout << diff << std::endl;
        };
        do_cont(tag<std::unordered_set<T, hasher>>{}, "std::unordered_set");
        do_cont(tag<unordered_node_set<T, hasher>>{}, "unordered_node_set");
        if constexpr (sizeof(T) <= 384) {
            do_cont(
                tag<unordered_dense_set<T, hasher>>{}, "unordered_dense_set");
        }
    };
    do_test(tag<bytes<16>>{}, "16 byte values");
    do_test(tag<bytes<64>>{}, "64 byte values");
    do_test(tag<bytes<256>>{}, "256 byte values");
    do_test(tag<bytes<512>>{}, "512 byte values");
#endif
}
