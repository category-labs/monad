#include <category/core/unordered_map.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp>  // NOLINT

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

TEST(UnorderedFlatMap, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_flat_map<int, int> map;
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

TEST(UnorderedFlatSet, works)
{
    using namespace MONAD_NAMESPACE;
    unordered_flat_set<int> set;
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
        auto do_cont = [&](auto tag2, const char *desc2) {
            using cont = typename decltype(tag2)::type;
            std::cout << "   Testing " << desc2 << " with " << desc << " ... "
                      << std::flush;
            auto begin = std::chrono::steady_clock::now();
            {
                cont c;
                for (auto i : values) {
                    c.insert(i);
                }
                for (size_t n = 0; n < 10; n++) {
                    for (auto i : values) {
                        volatile auto it = c.find(i);
                        (void)it;
                    }
                }
            }
            auto end = std::chrono::steady_clock::now();
            auto diff =
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
        if constexpr (sizeof(T) <= 48) {
            do_cont(tag<unordered_flat_set<T, hasher>>{}, "unordered_flat_set");
        }
    };
    do_test(tag<bytes<16>>{}, "16 byte values");
    do_test(tag<bytes<64>>{}, "64 byte values");
    do_test(tag<bytes<256>>{}, "256 byte values");
    do_test(tag<bytes<512>>{}, "512 byte values");
#endif
}
