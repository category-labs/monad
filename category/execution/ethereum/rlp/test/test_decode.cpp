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
