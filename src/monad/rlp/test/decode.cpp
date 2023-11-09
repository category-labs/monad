#include <monad/core/byte_string.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>

#include <gtest/gtest.h>

#include <string>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, DecodeAfterEncodeString)
{
    {
        std::string const empty_string = "";
        auto encoding = encode_string(to_byte_string_view(empty_string));
        byte_string decoding{};
        EXPECT_EQ(decode_string(decoding, encoding).size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(empty_string));
    }

    {
        std::string const short_string = "hello world";
        auto encoding = encode_string(to_byte_string_view(short_string));
        byte_string decoding{};
        EXPECT_EQ(decode_string(decoding, encoding).size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(short_string));
    }

    {
        std::string const long_string =
            "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
        auto encoding = encode_string(to_byte_string_view(long_string));
        byte_string decoding{};
        EXPECT_EQ(decode_string(decoding, encoding).size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(long_string));
    }
}
