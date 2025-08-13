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
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, ToBigEndianCompacted)
{
    auto bytes_1 = to_big_compact(uint16_t{1024});
    auto bytes_2 = to_big_compact(unsigned{1024});
    auto bytes_3 = to_big_compact(uint64_t{1024});

    EXPECT_EQ(bytes_1, monad::byte_string({0x04, 0x00}));
    EXPECT_EQ(bytes_1, bytes_2);
    EXPECT_EQ(bytes_2, bytes_3);
}

TEST(Rlp, EncodeString)
{
    // string with one char
    auto encoding = encode_string2(monad::byte_string({0x00}));
    EXPECT_EQ(encoding, monad::byte_string({0x00}));

    // simple string
    encoding = encode_string2(to_byte_string_view("dog"));
    EXPECT_EQ(encoding.size(), 4);
    EXPECT_EQ(encoding, monad::byte_string({0x83, 'd', 'o', 'g'}));

    // empty string
    encoding = encode_string2(to_byte_string_view(""));
    EXPECT_EQ(encoding, monad::byte_string({0x80}));

    // 56 character string
    auto const *const fifty_six_char_string =
        "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
    auto const fifty_six_char_string_encoding = monad::byte_string(
        {0xb8, 0x38, 'L', 'o', 'r', 'e', 'm', ' ', 'i', 'p', 's', 'u',
         'm',  ' ',  'd', 'o', 'l', 'o', 'r', ' ', 's', 'i', 't', ' ',
         'a',  'm',  'e', 't', ',', ' ', 'c', 'o', 'n', 's', 'e', 'c',
         't',  'e',  't', 'u', 'r', ' ', 'a', 'd', 'i', 'p', 'i', 's',
         'i',  'c',  'i', 'n', 'g', ' ', 'e', 'l', 'i', 't'});
    encoding = encode_string2(to_byte_string_view(fifty_six_char_string));
    EXPECT_EQ(encoding, fifty_six_char_string_encoding);

    std::array<unsigned char, 4> const an_array{0x00, 0x01, 0x02, 0x03};
    encoding = encode_string2(to_byte_string_view(an_array));
    EXPECT_EQ(encoding, monad::byte_string({0x84, 0x00, 0x01, 0x02, 0x03}));
}

TEST(Rlp, EncodeList)
{
    // Empty list
    auto encoding = encode_list2();
    EXPECT_EQ(encoding, monad::byte_string({0xc0}));

    // list of two strings
    encoding = encode_list2(
        encode_string2(to_byte_string_view("cat")),
        encode_string2(to_byte_string_view("dog")));
    EXPECT_EQ(
        encoding,
        monad::byte_string({0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g'}));
}
