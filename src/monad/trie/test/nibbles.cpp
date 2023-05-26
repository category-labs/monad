#include <gtest/gtest.h>

#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>

using namespace monad;
using namespace monad::trie;

TEST(Nibbles, SanityOdd)
{
    byte_string const nibble_array = {0x01, 0x02, 0x03, 0x04, 0x05};
    auto const nibbles = Nibbles(nibble_array);
    EXPECT_EQ(nibbles.rep, byte_string({5, 0x12, 0x34, 0x50}));
    EXPECT_EQ(nibbles.size(), 5);

    for (uint8_t i = 0; i < nibble_array.size(); ++i) {
        EXPECT_EQ(nibbles[i], nibble_array[i]);
    }
}

TEST(Nibbles, SanityEven)
{
    byte_string const nibble_array = {0x01, 0x02, 0x03, 0x04};
    auto const nibbles = Nibbles(nibble_array);
    EXPECT_EQ(nibbles.rep, byte_string({4, 0x12, 0x34}));
    EXPECT_EQ(nibbles.size(), 4);

    for (uint8_t i = 0; i < nibble_array.size(); ++i) {
        EXPECT_EQ(nibbles[i], nibble_array[i]);
    }
}

TEST(Nibbles, Comparison)
{
    auto const first = Nibbles(byte_string({0x01, 0x02, 0x03, 0x04}));
    auto const second = Nibbles(byte_string({0x01, 0x02, 0x03, 0x04, 0x05}));

    EXPECT_EQ(first, first);
    EXPECT_NE(first, second);

    EXPECT_TRUE(first < second);
    EXPECT_TRUE(first <= second);
    EXPECT_FALSE(first < first);
    EXPECT_FALSE(second < first);
    EXPECT_TRUE(second > first);
    EXPECT_TRUE(first >= first);
    EXPECT_TRUE(second >= first);

    auto const third = Nibbles(byte_string({0x01, 0x02, 0x03, 0x01}));
    EXPECT_TRUE(third < second);
    EXPECT_TRUE(third < first);
    EXPECT_TRUE(third <= second);
    EXPECT_TRUE(third <= first);
    EXPECT_FALSE(third > second);
    EXPECT_FALSE(third > first);

    auto view = third.substr(0);
    EXPECT_EQ(view, third);

    view = third.substr(2);
    EXPECT_NE(view, third);

    view = third.substr(3);
    EXPECT_NE(view, third);

    auto const fourth = Nibbles();
    EXPECT_TRUE(fourth < third);
    EXPECT_FALSE(fourth == third);
    EXPECT_FALSE(fourth > third);

    auto const fifth =
        Nibbles(byte_string({0x00, 0x01, 0x01, 0x02, 0x03, 0x01}));
    view = fifth.substr(2);
    EXPECT_NE(view, first);
    EXPECT_NE(view, second);
    EXPECT_EQ(view, third);

    auto another_view = third.substr(0);
    EXPECT_EQ(view, another_view);
}

TEST(Nibbles, OneNibble)
{
    auto const first = Nibbles(byte_string({0x01}));
    EXPECT_EQ(first.rep, byte_string({1, 0x10}));

    auto const second = Nibbles(byte_string({0x02}));
    EXPECT_EQ(second.rep, byte_string({1, 0x20}));

    EXPECT_NE(first, second);
    EXPECT_TRUE(first < second);

    auto const third = Nibbles(byte_string({0x01, 0x02}));
    EXPECT_EQ(third.rep, byte_string({2, 0x12}));

    EXPECT_NE(first, third);
    EXPECT_NE(second, third);

    EXPECT_FALSE(third < first);
    EXPECT_TRUE(third < second);
}

TEST(Nibbles, Addition)
{
    Nibbles const odd(byte_string({0x01, 0x02, 0x03}));
    Nibbles const even(byte_string({0x01, 0x02}));

    auto add = odd + even;
    Nibbles expected;
    expected.rep = byte_string({5, 0x12, 0x31, 0x20});
    EXPECT_EQ(add, expected);

    add = odd + odd;
    expected.rep = byte_string({6, 0x12, 0x31, 0x23});
    EXPECT_EQ(add, expected);

    add = even + even;
    expected.rep = byte_string({4, 0x12, 0x12});
    EXPECT_EQ(add, expected);

    Nibbles const first(
        byte_string{0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x3});
    Nibbles const second(byte_string{
        0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7,
        0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5,
        0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3,
        0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7});

    EXPECT_EQ(
        second.rep,
        byte_string({54,   0x23, 0x45, 0x67, 0x81, 0x23, 0x45, 0x67, 0x81, 0x23,
                     0x45, 0x67, 0x81, 0x23, 0x45, 0x67, 0x81, 0x23, 0x45, 0x67,
                     0x81, 0x23, 0x45, 0x67, 0x81, 0x23, 0x45, 0x67}));

    expected = Nibbles(byte_string{
        0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x3, 0x2, 0x3, 0x4, 0x5,
        0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2,
        0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7,
        0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4,
        0x5, 0x6, 0x7, 0x8, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7});
    add = first + second;
    EXPECT_EQ(add, expected);
}

TEST(Nibbles, EmptyNibbles)
{
    Nibbles empty;
    EXPECT_EQ(empty.size(), 0);
    EXPECT_TRUE(empty.empty());

    auto const one = Nibbles(byte_string({0x01}));
    EXPECT_TRUE(empty < one);

    auto add = empty + empty;
    EXPECT_EQ(add, empty);

    Nibbles non_empty(byte_string({0x01, 0x02}));
    add = empty + non_empty;
    EXPECT_EQ(add, non_empty);
}

TEST(Nibbles, LongestCommonPrefix)
{
    auto const first = Nibbles(byte_string({0x01, 0x02, 0x03, 0x04}));
    auto const second = Nibbles(byte_string({0x01, 0x02, 0x03}));

    EXPECT_EQ(longest_common_prefix_size(first, first), 4);
    EXPECT_EQ(longest_common_prefix_size(first, second), 3);

    auto const third = Nibbles(byte_string({0x02, 0x03, 0x04}));

    EXPECT_EQ(longest_common_prefix_size(first, third), 0);
}

TEST(Nibbles, View)
{
    auto const nibbles = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});
    auto view = NibblesView{nibbles};
    EXPECT_EQ(view.size(), 5);
    EXPECT_EQ(view.start, 0);
    EXPECT_EQ(view.rep, nibbles.rep);

    view = nibbles.substr(3);
    EXPECT_EQ(view.size(), 2);
    EXPECT_EQ(view.start, 3);
    EXPECT_EQ(view.rep, nibbles.rep);

    EXPECT_EQ(view[0], 0x04);
    EXPECT_EQ(view[1], 0x05);
}

TEST(Nibbles, Serialize)
{
    auto const nibbles = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});
    KeyBuffer buf;
    serialize_nibbles(buf, nibbles);
    EXPECT_EQ(buf.view(), byte_string({5, 0x12, 0x34, 0x50}));
    auto view = NibblesView{nibbles};

    serialize_nibbles(buf, view);
    EXPECT_EQ(buf.view(), byte_string({5, 0x12, 0x34, 0x50}));

    view = nibbles.substr(1);
    serialize_nibbles(buf, view);
    EXPECT_EQ(buf.view(), byte_string({4, 0x23, 0x45}));

    view = nibbles.prefix(3);
    serialize_nibbles(buf, view);
    EXPECT_EQ(buf.view(), byte_string({3, 0x12, 0x30}));
}

TEST(Nibbles, DeserializeOdd)
{
    auto const nibbles = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});
    KeyBuffer buf;
    serialize_nibbles(buf, nibbles);

    auto const [deserialized, size] = deserialize_nibbles(buf.view());
    EXPECT_EQ(size, 4);
    EXPECT_EQ(deserialized, nibbles);
}

TEST(Nibbles, DeserializeEven)
{
    auto const nibbles = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04});
    KeyBuffer buf;
    serialize_nibbles(buf, nibbles);

    auto const [deserialized, size] = deserialize_nibbles(buf.view());
    EXPECT_EQ(size, 3);
    EXPECT_EQ(deserialized, nibbles);
}

TEST(Nibbles, StartsWith)
{
    auto const nibbles = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});

    auto prefix = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});
    EXPECT_TRUE(nibbles.startswith(prefix));

    prefix = Nibbles();
    EXPECT_TRUE(nibbles.startswith(prefix));

    prefix = Nibbles(byte_string{0x01});
    EXPECT_TRUE(nibbles.startswith(prefix));

    prefix = Nibbles(byte_string{0x01, 0x02, 0x03});
    EXPECT_TRUE(nibbles.startswith(prefix));

    prefix = Nibbles(byte_string{0x01, 0x02, 0x02});
    EXPECT_FALSE(nibbles.startswith(prefix));
    prefix = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05, 0x06});
    EXPECT_FALSE(nibbles.startswith(prefix));

    prefix = Nibbles(byte_string{0x01, 0x02});
    EXPECT_TRUE(nibbles.startswith(prefix));
}

TEST(Nibbles, PushAndPopBack)
{
    Nibbles nibbles;
    nibbles.push_back(0x2);
    EXPECT_EQ(nibbles, Nibbles(byte_string{0x2}));

    nibbles.push_back(0x3);
    EXPECT_EQ(nibbles, Nibbles(byte_string{0x2, 0x3}));

    nibbles.push_back(0x4);
    EXPECT_EQ(nibbles, Nibbles(byte_string{0x2, 0x3, 0x4}));

    nibbles.pop_back();
    EXPECT_EQ(nibbles, Nibbles(byte_string{0x2, 0x3}));

    nibbles.pop_back();
    nibbles.pop_back();

    EXPECT_EQ(nibbles, Nibbles());
    EXPECT_TRUE(nibbles.empty());
}
