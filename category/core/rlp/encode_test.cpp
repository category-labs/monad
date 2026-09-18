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

#include <category/core/rlp/encode.hpp>

#include <category/core/byte_string.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <span>

using monad::byte_string;
using monad::byte_string_view;

TEST(rlp, impl_length_length)
{
    size_t result;

    result = monad::rlp::impl::length_length(0);
    EXPECT_EQ(result, 0);

    result = monad::rlp::impl::length_length(1);
    EXPECT_EQ(result, 1);

    result = monad::rlp::impl::length_length(255);
    EXPECT_EQ(result, 1);

    result = monad::rlp::impl::length_length(256);
    EXPECT_EQ(result, 2);

    result = monad::rlp::impl::length_length(65535);
    EXPECT_EQ(result, 2);

    result = monad::rlp::impl::length_length(65536);
    EXPECT_EQ(result, 3);

    result = monad::rlp::impl::length_length((1UL << 56) - 1);
    EXPECT_EQ(result, 7);

    result = monad::rlp::impl::length_length(1UL << 56);
    EXPECT_EQ(result, 8);

    result = monad::rlp::impl::length_length(0xFFFFFFFFFFFFFFFFUL);
    EXPECT_EQ(result, 8);
}

TEST(rlp, impl_encode_length)
{
    unsigned char buf[8];
    std::span<unsigned char> result;

    result = monad::rlp::impl::encode_length(buf, 0);
    EXPECT_EQ(result.data() - buf, 0);

    result = monad::rlp::impl::encode_length(buf, 1);
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string{1});

    result = monad::rlp::impl::encode_length(buf, 255);
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string{255});

    result = monad::rlp::impl::encode_length(buf, 256);
    EXPECT_EQ(result.data() - buf, 2);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({1, 0}));

    result = monad::rlp::impl::encode_length(buf, 258);
    EXPECT_EQ(result.data() - buf, 2);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({1, 2}));

    result = monad::rlp::impl::encode_length(buf, 0xFFFFFFFFFFFFFFFFUL);
    EXPECT_EQ(result.data() - buf, 8);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) ==
        byte_string({0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}));
}

TEST(rlp, impl_encode_length_compact_preserves_tail)
{
    for (size_t len = 0; len <= sizeof(size_t); ++len) {
        unsigned char buf[sizeof(size_t) + 1];
        std::fill(std::begin(buf), std::end(buf), 0xaa);
        size_t const value = len == 0 ? 0 : size_t{1} << (8 * (len - 1));
        auto const remaining = monad::rlp::impl::encode_length_compact(
            std::span{buf}.first(len), value);
        EXPECT_TRUE(remaining.empty());
        if (len != 0) {
            EXPECT_EQ(buf[0], 1);
            for (size_t i = 1; i < len; ++i) {
                EXPECT_EQ(buf[i], 0);
            }
        }
        for (size_t i = len; i < sizeof(buf); ++i) {
            EXPECT_EQ(buf[i], 0xaa);
        }
    }
}

TEST(rlp, encode_list_prefix_compact_preserves_payload)
{
    for (size_t const size : {0u, 55u, 56u, 255u, 256u, 65535u, 65536u}) {
        byte_string node(monad::rlp::list_length(size), 0xaa);
        size_t const header_len = node.size() - size;
        auto const remaining = monad::rlp::encode_list_prefix_compact(
            std::span{node}.first(header_len), size);
        EXPECT_TRUE(remaining.empty());
        EXPECT_EQ(node.substr(header_len), byte_string(size, 0xaa));
        unsigned char expected[1 + sizeof(size_t)];
        auto const rest = monad::rlp::encode_list_prefix(expected, size);
        EXPECT_EQ(sizeof(expected) - rest.size(), header_len);
        EXPECT_EQ(
            node.substr(0, header_len), byte_string(expected, header_len));
    }
}

TEST(rlp, string_length)
{
    size_t result;

    constexpr unsigned char a1[] = {1};
    result = monad::rlp::string_length(monad::to_byte_string_view(a1));
    EXPECT_EQ(result, 1);

    constexpr unsigned char a2[] = {128};
    result = monad::rlp::string_length(monad::to_byte_string_view(a2));
    EXPECT_EQ(result, 2);

    result = monad::rlp::string_length({});
    EXPECT_EQ(result, 1);

    constexpr unsigned char a3[] = {1, 2};
    result = monad::rlp::string_length(monad::to_byte_string_view(a3));
    EXPECT_EQ(result, 3);

    result = monad::rlp::string_length(byte_string(55, 1));
    EXPECT_EQ(result, 56);

    result = monad::rlp::string_length(byte_string(56, 1));
    EXPECT_EQ(result, 58);
}

TEST(rlp, encode_string)
{
    unsigned char buf[256];
    std::span<unsigned char> result;

    result = monad::rlp::encode_string(buf, byte_string({1}));
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({1}));

    result = monad::rlp::encode_string(buf, byte_string({128}));
    EXPECT_EQ(result.data() - buf, 2);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) == byte_string({129, 128}));

    result = monad::rlp::encode_string(buf, byte_string{});
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({128}));

    result = monad::rlp::encode_string(buf, byte_string_view{});
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({128}));

    result = monad::rlp::encode_string(buf, byte_string({1, 2}));
    EXPECT_EQ(result.data() - buf, 3);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) == byte_string({130, 1, 2}));

    result = monad::rlp::encode_string(buf, byte_string(55, 1));
    EXPECT_EQ(result.data() - buf, 56);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) ==
        byte_string({183}) + byte_string(55, 1));

    result = monad::rlp::encode_string(buf, byte_string(56, 1));
    EXPECT_EQ(result.data() - buf, 58);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) ==
        byte_string({184, 56}) + byte_string(56, 1));
}

TEST(rlp, list_length)
{
    size_t result;

    result = monad::rlp::list_length(0);
    EXPECT_EQ(result, 1);

    result = monad::rlp::list_length(1);
    EXPECT_EQ(result, 2);

    result = monad::rlp::list_length(2);
    EXPECT_EQ(result, 3);

    result = monad::rlp::list_length(55);
    EXPECT_EQ(result, 56);

    result = monad::rlp::list_length(56);
    EXPECT_EQ(result, 58);
}

TEST(rlp, encode_list)
{
    unsigned char buf[256];
    std::span<unsigned char> result;

    result = monad::rlp::encode_list(buf, byte_string{});
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string{192});

    result = monad::rlp::encode_list(buf, byte_string_view{});
    EXPECT_EQ(result.data() - buf, 1);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string{192});

    result = monad::rlp::encode_list(buf, byte_string{1});
    EXPECT_EQ(result.data() - buf, 2);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({193, 1}));

    result = monad::rlp::encode_list(buf, byte_string{1, 2});
    EXPECT_EQ(result.data() - buf, 3);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) == byte_string({194, 1, 2}));

    result = monad::rlp::encode_list(buf, byte_string(55, 1));
    EXPECT_EQ(result.data() - buf, 56);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) ==
        byte_string({247}) + byte_string(55, 1));

    result = monad::rlp::encode_list(buf, byte_string(56, 1));
    EXPECT_EQ(result.data() - buf, 58);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) ==
        byte_string({248, 56}) + byte_string(56, 1));
}
