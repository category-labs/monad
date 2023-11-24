#include <monad/core/byte_string.hpp>
#include <monad/test/make_nibbles.hpp>
#include <monad/trie/compact_encode.hpp>
#include <monad/trie/nibbles.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::trie;

TEST(CompactEncoding, Sanity)
{
    auto path = test::make_nibbles({0x12, 0x34, 0x50}, 5);

    EXPECT_EQ(compact_encode(path, false), byte_string({0x11, 0x23, 0x45}));
    EXPECT_EQ(compact_encode(path, true), byte_string({0x31, 0x23, 0x45}));

    path = test::make_nibbles({0x01, 0x23, 0x45});

    EXPECT_EQ(
        compact_encode(path, false), byte_string({0x00, 0x01, 0x23, 0x45}));
    EXPECT_EQ(
        compact_encode(path, true), byte_string({0x20, 0x01, 0x23, 0x45}));

    path = test::make_nibbles({0x0f, 0x1c, 0xb8});

    EXPECT_EQ(
        compact_encode(path, false), byte_string({0x00, 0x0f, 0x1c, 0xb8}));
    EXPECT_EQ(
        compact_encode(path, true), byte_string({0x20, 0x0f, 0x1c, 0xb8}));

    path = test::make_nibbles({0xf1, 0xcb, 0x80}, 5);
    EXPECT_EQ(compact_encode(path, false), byte_string({0x1f, 0x1c, 0xb8}));
    EXPECT_EQ(compact_encode(path, true), byte_string({0x3f, 0x1c, 0xb8}));
}
