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

#include <cstddef>
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

    result = monad::rlp::encode_string(buf, byte_string({1, 2}));
    EXPECT_EQ(result.data() - buf, 3);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) == byte_string({130, 1, 2}));

    result = monad::rlp::encode_string(buf, byte_string(55, 1));
    EXPECT_EQ(result.data() - buf, 56);
    {
        auto expected = byte_string({183});
        auto suffix = byte_string(55, 1);
        expected.insert(expected.end(), suffix.begin(), suffix.end());
        EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string_view(
                                                           expected.data(),
                                                           expected.size()));
    }

    result = monad::rlp::encode_string(buf, byte_string(56, 1));
    EXPECT_EQ(result.data() - buf, 58);
    {
        auto expected = byte_string({184, 56});
        auto suffix = byte_string(56, 1);
        expected.insert(expected.end(), suffix.begin(), suffix.end());
        EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string_view(
                                                           expected.data(),
                                                           expected.size()));
    }
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

    result = monad::rlp::encode_list(buf, byte_string{1});
    EXPECT_EQ(result.data() - buf, 2);
    EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string({193, 1}));

    result = monad::rlp::encode_list(buf, byte_string{1, 2});
    EXPECT_EQ(result.data() - buf, 3);
    EXPECT_TRUE(
        byte_string_view(buf, result.data()) == byte_string({194, 1, 2}));

    result = monad::rlp::encode_list(buf, byte_string(55, 1));
    EXPECT_EQ(result.data() - buf, 56);
    {
        auto expected = byte_string({247});
        auto suffix = byte_string(55, 1);
        expected.insert(expected.end(), suffix.begin(), suffix.end());
        EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string_view(
                                                           expected.data(),
                                                           expected.size()));
    }

    result = monad::rlp::encode_list(buf, byte_string(56, 1));
    EXPECT_EQ(result.data() - buf, 58);
    {
        auto expected = byte_string({248, 56});
        auto suffix = byte_string(56, 1);
        expected.insert(expected.end(), suffix.begin(), suffix.end());
        EXPECT_TRUE(byte_string_view(buf, result.data()) == byte_string_view(
                                                           expected.data(),
                                                           expected.size()));
    }
}
