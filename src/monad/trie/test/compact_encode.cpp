#include <monad/trie/compact_encode.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::trie;

TEST(CompactEncoding, Sanity)
{
    auto path = Nibbles(byte_string{0x01, 0x02, 0x03, 0x04, 0x05});

    EXPECT_EQ(compact_encode(path, false), byte_string({0x11, 0x23, 0x45}));
    EXPECT_EQ(compact_encode(path, true), byte_string({0x31, 0x23, 0x45}));

    path = Nibbles(byte_string{0x00, 0x01, 0x02, 0x03, 0x04, 0x05});

    EXPECT_EQ(
        compact_encode(path, false), byte_string({0x00, 0x01, 0x23, 0x45}));
    EXPECT_EQ(
        compact_encode(path, true), byte_string({0x20, 0x01, 0x23, 0x45}));

    path = Nibbles(byte_string{0x00, 0x0f, 0x01, 0x0c, 0x0b, 0x08});

    EXPECT_EQ(
        compact_encode(path, false), byte_string({0x00, 0x0f, 0x1c, 0xb8}));
    EXPECT_EQ(
        compact_encode(path, true), byte_string({0x20, 0x0f, 0x1c, 0xb8}));

    path = Nibbles(byte_string{0x0f, 0x01, 0x0c, 0x0b, 0x08});
    EXPECT_EQ(compact_encode(path, false), byte_string({0x1f, 0x1c, 0xb8}));
    EXPECT_EQ(compact_encode(path, true), byte_string({0x3f, 0x1c, 0xb8}));
}
