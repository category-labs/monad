#include <gtest/gtest.h>

#include <monad/trie/nibbles.hpp>

using namespace monad;
using namespace monad::trie;

TEST(Nibbles, SanityOdd)
{
    byte_string const nibble_array = {0x01, 0x02, 0x03, 0x04, 0x05};
    auto const nibbles = Nibbles(nibble_array, Nibbles::FromNibbleArray{});
    EXPECT_EQ(nibbles.bytes, byte_string({0x12, 0x34, 0x50}));
    EXPECT_EQ(nibbles.size(), 5);

    for (size_t i = 0; i < nibble_array.size(); ++i) {
        EXPECT_EQ(nibbles[i], nibble_array[i]);
    }
}

TEST(Nibbles, SanityEven)
{
    byte_string const nibble_array = {0x01, 0x02, 0x03, 0x04};
    auto const nibbles = Nibbles(nibble_array, Nibbles::FromNibbleArray{});
    EXPECT_EQ(nibbles.bytes, byte_string({0x12, 0x34}));
    EXPECT_EQ(nibbles.size(), 4);

    for (size_t i = 0; i < nibble_array.size(); ++i) {
        EXPECT_EQ(nibbles[i], nibble_array[i]);
    }
}

TEST(Nibbles, Comparison)
{
    auto const first = Nibbles(
        byte_string({0x01, 0x02, 0x03, 0x04}), Nibbles::FromNibbleArray{});
    auto const second = Nibbles(
        byte_string({0x01, 0x02, 0x03, 0x04, 0x05}),
        Nibbles::FromNibbleArray{});

    EXPECT_EQ(first, first);
    EXPECT_NE(first, second);

    EXPECT_TRUE(first < second);
    EXPECT_FALSE(first < first);
    EXPECT_FALSE(second < first);

    auto const third = Nibbles(
        byte_string({0x01, 0x02, 0x03, 0x01}), Nibbles::FromNibbleArray{});
    EXPECT_TRUE(third < second);
    EXPECT_TRUE(third < first);
}

TEST(Nibbles, OneNibble)
{
    auto const first = Nibbles(byte_string({0x01}), Nibbles::FromNibbleArray{});
    EXPECT_EQ(first.bytes, byte_string({0x10}));

    auto const second =
        Nibbles(byte_string({0x02}), Nibbles::FromNibbleArray{});
    EXPECT_EQ(second.bytes, byte_string({0x20}));

    EXPECT_NE(first, second);
    EXPECT_TRUE(first < second);

    auto const third =
        Nibbles(byte_string({0x01, 0x02}), Nibbles::FromNibbleArray{});
    EXPECT_EQ(third.bytes, byte_string({0x12}));

    EXPECT_NE(first, third);
    EXPECT_NE(second, third);

    EXPECT_FALSE(third < first);
    EXPECT_TRUE(third < second);
}

TEST(Nibbles, EmptyNibbles)
{
    Nibbles empty({}, Nibbles::FromNibbleArray{});
    EXPECT_EQ(empty.size(), 0);
    EXPECT_TRUE(empty.empty());

    auto const one = Nibbles(byte_string({0x01}), Nibbles::FromNibbleArray{});
    EXPECT_TRUE(empty < one);
}
