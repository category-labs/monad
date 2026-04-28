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

#include <category/core/byte_string.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <gtest/gtest.h>

#include <string>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, DecodeAfterEncodeString)
{
    {
        std::string const empty_string = "";
        auto encoding = encode_string2(to_byte_string_view(empty_string));

        byte_string_view encoded_string_view{encoding};
        auto const decoded_string = decode_string(encoded_string_view);
        ASSERT_FALSE(decoded_string.has_error());
        EXPECT_EQ(encoded_string_view.size(), 0);
        EXPECT_EQ(decoded_string.value(), to_byte_string_view(empty_string));
    }

    {
        std::string const short_string = "hello world";
        auto encoding = encode_string2(to_byte_string_view(short_string));

        byte_string_view encoded_string_view{encoding};
        auto const decoded_string = decode_string(encoded_string_view);
        ASSERT_FALSE(decoded_string.has_error());
        EXPECT_EQ(encoded_string_view.size(), 0);
        EXPECT_EQ(decoded_string.value(), to_byte_string_view(short_string));
    }

    {
        std::string const long_string =
            "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
        auto encoding = encode_string2(to_byte_string_view(long_string));

        byte_string_view encoded_string_view2{encoding};
        auto const decoded_string = decode_string(encoded_string_view2);
        ASSERT_FALSE(decoded_string.has_error());
        EXPECT_EQ(encoded_string_view2.size(), 0);
        EXPECT_EQ(decoded_string.value(), to_byte_string_view(long_string));
    }
}

TEST(Rlp, ParseMetadata)
{
    // String payload
    {
        auto encoding = encode_string2(to_byte_string_view("dog"));
        byte_string_view enc{encoding};

        auto const result = parse_metadata(enc);
        ASSERT_FALSE(result.has_error());
        EXPECT_EQ(result.value().first, RlpType::String);
        EXPECT_EQ(result.value().second, to_byte_string_view("dog"));
        EXPECT_EQ(enc.size(), 0);
    }

    // List payload
    {
        auto const inner =
            byte_string({0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g'});
        auto encoding = encode_list2(
            encode_string2(to_byte_string_view("cat")),
            encode_string2(to_byte_string_view("dog")));
        byte_string_view enc{encoding};

        auto const result = parse_metadata(enc);
        ASSERT_FALSE(result.has_error());
        EXPECT_EQ(result.value().first, RlpType::List);
        EXPECT_EQ(result.value().second, byte_string_view{inner});
        EXPECT_EQ(enc.size(), 0);
    }

    // Empty input
    {
        byte_string_view enc{};
        auto const result = parse_metadata(enc);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), DecodeError::InputTooShort);
    }

    // Long string payload (>55 bytes) - exercises the [0xb8, 0xbf] branch
    {
        std::string const long_string(100, 'a');
        auto encoding = encode_string2(to_byte_string_view(long_string));
        ASSERT_FALSE(encoding.empty());
        ASSERT_GE(encoding[0], 0xb8);
        ASSERT_LE(encoding[0], 0xbf);

        byte_string_view enc{encoding};
        auto const result = parse_metadata(enc);
        ASSERT_FALSE(result.has_error());
        EXPECT_EQ(result.value().first, RlpType::String);
        EXPECT_EQ(result.value().second, to_byte_string_view(long_string));
        EXPECT_EQ(enc.size(), 0);
    }

    // Long list payload (>55 bytes) - exercises the [0xf8, 0xff] branch
    {
        std::string const item(60, 'x');
        auto encoding = encode_list2(
            encode_string2(to_byte_string_view(item)),
            encode_string2(to_byte_string_view(item)));
        ASSERT_FALSE(encoding.empty());
        ASSERT_GE(encoding[0], 0xf8);

        byte_string_view enc{encoding};
        auto const result = parse_metadata(enc);
        ASSERT_FALSE(result.has_error());
        EXPECT_EQ(result.value().first, RlpType::List);
        EXPECT_EQ(enc.size(), 0);
    }

    // parse_string_metadata on a list-prefix input -> TypeUnexpected
    {
        auto encoding = encode_list2(
            encode_string2(to_byte_string_view("cat")),
            encode_string2(to_byte_string_view("dog")));
        byte_string_view enc{encoding};

        auto const result = parse_string_metadata(enc);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), DecodeError::TypeUnexpected);
    }

    // parse_list_metadata on a string-prefix input -> TypeUnexpected
    {
        auto encoding = encode_string2(to_byte_string_view("hello"));
        byte_string_view enc{encoding};

        auto const result = parse_list_metadata(enc);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), DecodeError::TypeUnexpected);
    }
}
