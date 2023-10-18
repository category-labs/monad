#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp, DecodeUnsigned)
{
    auto res = decode_length(monad::byte_string({0x00}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 0);
    res = decode_length(monad::byte_string({0x0f}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 15);
    res = decode_length(monad::byte_string({0x7a}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 122);
    res = decode_length(monad::byte_string({0x04, 0x00}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 1024);
    res = decode_length(monad::byte_string({0x03, 0x04}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 772);
    res = decode_length(monad::byte_string({0x02, 0x29}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 553);
    res = decode_length(monad::byte_string({0x04, 0x98}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 1176);
    res = decode_length(monad::byte_string({0x41, 0x42}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 16706);
    res = decode_length(monad::byte_string({0x7b, 0x2a}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 31530);
    res = decode_length(monad::byte_string({0xff, 0xff}));
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res.assume_value(), 65535);
}

TEST(Rlp, DecodeAfterEncodeString)
{
    {
        std::string empty_string = "";
        auto encoding = encode_string(to_byte_string_view(empty_string));
        byte_string decoding{};
        auto const res = decode_string(decoding, encoding);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(empty_string));
    }

    {
        std::string short_string = "hello world";
        auto encoding = encode_string(to_byte_string_view(short_string));
        byte_string decoding{};
        auto const res = decode_string(decoding, encoding);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(short_string));
    }

    {
        std::string long_string =
            "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
        auto encoding = encode_string(to_byte_string_view(long_string));
        byte_string decoding{};
        auto const res = decode_string(decoding, encoding);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.assume_value().size(), 0);
        EXPECT_EQ(decoding, to_byte_string_view(long_string));
    }
}
