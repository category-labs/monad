#include <monad/core/byte_string.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>
#include <monad/rlp/util.hpp>

#include <gtest/gtest.h>

#include <string>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, DecodeUnsigned)
{
    EXPECT_EQ(0, decode_length(monad::byte_string({0x00})));
    EXPECT_EQ(15, decode_length(monad::byte_string({0x0f})));
    EXPECT_EQ(122, decode_length(monad::byte_string({0x7a})));
    EXPECT_EQ(1024, decode_length(monad::byte_string({0x04, 0x00})));
    EXPECT_EQ(772, decode_length(monad::byte_string({0x03, 0x04})));
    EXPECT_EQ(553, decode_length(monad::byte_string({0x02, 0x29})));
    EXPECT_EQ(1176, decode_length(monad::byte_string({0x04, 0x98})));
    EXPECT_EQ(16706, decode_length(monad::byte_string({0x41, 0x42})));
    EXPECT_EQ(31530, decode_length(monad::byte_string({0x7b, 0x2a})));
    EXPECT_EQ(65535, decode_length(monad::byte_string({0xff, 0xff})));
}

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
