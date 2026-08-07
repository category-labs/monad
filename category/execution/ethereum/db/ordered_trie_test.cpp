// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/ethereum/db/ordered_trie.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <random>
#include <span>
#include <vector>

using namespace monad;
using namespace monad::rlp;

namespace
{
    // Assemble expected nodes forwards using the owning RLP encoders.
    byte_string reference(byte_string const &node)
    {
        if (node.size() < 32) {
            return node;
        }
        auto const hash = to_bytes(keccak256(node));
        return encode_string2({hash.bytes, sizeof(hash.bytes)});
    }

    byte_string leaf(byte_string const &path, byte_string const &value)
    {
        return encode_list2(encode_string2(path), encode_string2(value));
    }

    byte_string
    actual_ref(std::vector<monad::detail::Item> const &items, unsigned depth)
    {
        std::array<unsigned char, 34> buffer;
        buffer.fill(0xaa);
        auto const dest = std::span{buffer}.subspan<1, 32>();
        size_t const written =
            monad::detail::node_ref(items, 0, items.size(), depth, dest);
        EXPECT_LE(written, 32);
        EXPECT_EQ(buffer.front(), 0xaa);
        EXPECT_EQ(buffer.back(), 0xaa);
        auto const encoded = dest.last(written);
        EXPECT_TRUE(std::ranges::all_of(
            dest.first(dest.size() - written),
            [](unsigned char b) { return b == 0xaa; }));
        // A 32-byte result is a raw hash; the caller supplies the RLP string
        // header, so add it here to compare against reference().
        if (written == 32) {
            return encode_string2({encoded.data(), encoded.size()});
        }
        return {encoded.data(), encoded.size()};
    }
}

TEST(BodyRoots, MaxSizeTIndexFitsKeyBuffer)
{
    struct
    {
        unsigned char before = 0xaa;
        unsigned char key[1 + sizeof(size_t)]{};
        unsigned char after = 0xbb;
    } buffer;

    constexpr auto index = std::numeric_limits<size_t>::max();
    auto const remaining = encode_unsigned(buffer.key, index);

    EXPECT_TRUE(remaining.empty());
    EXPECT_EQ(remaining.data(), buffer.key + sizeof(buffer.key));
    EXPECT_EQ(buffer.key[0], 0x80 + sizeof(size_t));
    for (size_t i = 1; i < sizeof(buffer.key); ++i) {
        EXPECT_EQ(buffer.key[i], 0xff);
    }
    EXPECT_EQ(buffer.before, 0xaa);
    EXPECT_EQ(buffer.after, 0xbb);

    monad::detail::Item const item{index, {}};
    EXPECT_EQ(item.key_len, sizeof(item.key));
    EXPECT_EQ(
        byte_string_view(item.key, item.key_len),
        byte_string_view(buffer.key, sizeof(buffer.key)));
    EXPECT_EQ(item.nib().nibble_size(), 2 * sizeof(item.key));

    byte_string_view encoded{buffer.key, sizeof(buffer.key)};
    auto const decoded = decode_unsigned<size_t>(encoded);
    ASSERT_FALSE(decoded.has_error());
    EXPECT_EQ(decoded.value(), index);
    EXPECT_TRUE(encoded.empty());
}

TEST(BodyRoots, InlineKeysMatchUnsignedEncoding)
{
    auto const check = [](size_t const index) {
        monad::detail::Item const item{index, {}};
        auto const expected = encode_unsigned(index);
        EXPECT_EQ(byte_string_view(item.key, item.key_len), expected);
        EXPECT_EQ(item.nib(), mpt::NibblesView{expected});
    };
    for (size_t index = 0; index <= 256; ++index) {
        check(index);
    }
    for (unsigned byte = 1; byte < sizeof(size_t); ++byte) {
        size_t const boundary = size_t{1} << (8 * byte);
        check(boundary - 1);
        check(boundary);
        check(boundary + 1);
    }
    std::mt19937_64 random{1234};
    for (unsigned i = 0; i < 1000; ++i) {
        check(static_cast<size_t>(random()));
    }
}

TEST(BodyRoots, EmptyRoot)
{
    EXPECT_EQ(ordered_trie_root(std::span<byte_string const>{}), NULL_ROOT);
}

TEST(BodyRoots, LeafEncodingBoundaries)
{
    for (size_t const len :
         {0u,
          1u,
          26u,
          27u,
          28u,
          29u,
          30u,
          31u,
          32u,
          54u,
          55u,
          56u,
          255u,
          256u,
          65535u,
          65536u}) {
        for (unsigned const fill : {0x00u, 0x7fu, 0x80u, 0xffu}) {
            byte_string const value(len, static_cast<unsigned char>(fill));
            std::vector<monad::detail::Item> const items{{0, value}};
            auto const expected = leaf({0x20, 0x80}, value);
            EXPECT_EQ(actual_ref(items, 0), reference(expected));
            std::array<byte_string_view, 1> const values{value};
            EXPECT_EQ(
                ordered_trie_root(std::span{values}),
                to_bytes(keccak256(expected)));
        }
    }
}

TEST(BodyRoots, FullBranchUsesMaximumBuffer)
{
    byte_string const value(56, 0xaa);
    std::vector<monad::detail::Item> items;
    byte_string children;
    for (size_t index = 0x10; index < 0x20; ++index) {
        items.emplace_back(index, value);
        children += reference(leaf({0x20}, value));
    }
    children.push_back(0x80);
    auto const expected = encode_list2(children);
    ASSERT_EQ(expected.size(), 532);
    EXPECT_EQ(actual_ref(items, 1), reference(expected));
}

TEST(BodyRoots, ExtensionWithInlineAndHashedChildren)
{
    for (size_t const value_len : {0u, 56u}) {
        byte_string const value(value_len, 0xaa);
        for (size_t const first : {0x12u, 0x1234u}) {
            std::vector<monad::detail::Item> const items{
                {first, value}, {first + 1, value}};
            byte_string children;
            unsigned const slot = first == 0x12 ? 2 : 4;
            for (unsigned i = 0; i < 16; ++i) {
                children += (i == slot || i == slot + 1)
                                ? reference(leaf({0x20}, value))
                                : byte_string{0x80};
            }
            children.push_back(0x80);
            auto const branch = encode_list2(children);
            byte_string const path = first == 0x12
                                         ? byte_string{0x11}
                                         : byte_string{0x18, 0x21, 0x23};
            auto const expected =
                encode_list2(encode_string2(path), reference(branch));
            EXPECT_EQ(actual_ref(items, 0), reference(expected));
        }
    }
}

TEST(BodyRoots, TwoItemRootAndSpanOverloads)
{
    std::vector<byte_string> values{{0x01}, byte_string(56, 0xaa)};
    byte_string children;
    for (unsigned i = 0; i < 16; ++i) {
        if (i == 0) {
            children += reference(leaf({0x31}, values[1]));
        }
        else if (i == 8) {
            children += reference(leaf({0x30}, values[0]));
        }
        else {
            children.push_back(0x80);
        }
    }
    children.push_back(0x80);
    auto const expected = to_bytes(keccak256(encode_list2(children)));
    EXPECT_EQ(ordered_trie_root(std::span{values}), expected);
    EXPECT_EQ(
        ordered_trie_root(std::span<byte_string const>{values}), expected);
    std::array<byte_string_view, 2> views{values[0], values[1]};
    EXPECT_EQ(ordered_trie_root(std::span{views}), expected);
    EXPECT_EQ(
        ordered_trie_root(std::span<byte_string_view const>{views}), expected);
}

TEST(BodyRoots, EvenLengthExtension)
{
    byte_string const value{0x01};
    std::vector<monad::detail::Item> const items{{0x80, value}, {0x90, value}};
    byte_string children;
    for (unsigned i = 0; i < 16; ++i) {
        children += (i == 8 || i == 9) ? reference(leaf({0x30}, value))
                                       : byte_string{0x80};
    }
    children.push_back(0x80);
    auto const expected = encode_list2(
        encode_string2(byte_string{0x00, 0x81}),
        reference(encode_list2(children)));
    EXPECT_EQ(actual_ref(items, 0), reference(expected));
}
