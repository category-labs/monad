#include <monad/core/byte_string.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

#include <gtest/gtest.h>

#include <string>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, DecodeAfterEncodeString)
{
    {
        std::string const empty_string = "";
        auto encoding = encode_string2(to_byte_string_view(empty_string));
        byte_string decoding{};
        auto const remaining = decode_string(decoding, encoding);
        ASSERT_FALSE(remaining.has_error());
        EXPECT_EQ(remaining.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(empty_string));
    }

    {
        std::string const short_string = "hello world";
        auto encoding = encode_string2(to_byte_string_view(short_string));
        byte_string decoding{};
        auto const remaining = decode_string(decoding, encoding);
        ASSERT_FALSE(remaining.has_error());
        EXPECT_EQ(remaining.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(short_string));
    }

    {
        std::string const long_string =
            "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
        auto encoding = encode_string2(to_byte_string_view(long_string));
        byte_string decoding{};
        auto const remaining = decode_string(decoding, encoding);
        ASSERT_FALSE(remaining.has_error());
        EXPECT_EQ(remaining.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(long_string));
    }
}
