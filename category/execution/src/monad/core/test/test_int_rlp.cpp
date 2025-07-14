#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp_Number, DecodeUnsigned)
{
    {
        auto const remaining = decode_length(monad::byte_string({}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 0);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x00}));
        EXPECT_TRUE(
            remaining.has_error() &&
            remaining.assume_error() == DecodeError::LeadingZero);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x0f}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 15);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x7a}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 122);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x04, 0x00}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 1024);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x03, 0x04}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 772);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x02, 0x29}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 553);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x04, 0x98}));
        EXPECT_TRUE(!remaining.has_error() && remaining.assume_value() == 1176);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x41, 0x42}));
        EXPECT_TRUE(
            !remaining.has_error() && remaining.assume_value() == 16706);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0x7b, 0x2a}));
        EXPECT_TRUE(
            !remaining.has_error() && remaining.assume_value() == 31530);
    }

    {
        auto const remaining = decode_length(monad::byte_string({0xff, 0xff}));
        EXPECT_TRUE(
            !remaining.has_error() && remaining.assume_value() == 65535);
    }
}

TEST(Rlp_Number, DecodeEncodeUnsigned)
{
    // integer 0
    {
        auto const encoding = encode_unsigned(0u);
        EXPECT_EQ(encoding, monad::byte_string({0x80}));

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint8_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(decoded_unsigned.value(), 0u);
    }

    // char 0
    {
        auto const encoding = encode_unsigned(uint8_t{0});
        EXPECT_EQ(encoding, monad::byte_string({0x80}));

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint8_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(decoded_unsigned.value(), uint8_t{0});
    }

    // integer 15
    {
        auto const encoding = encode_unsigned(15u);
        EXPECT_EQ(encoding, monad::byte_string({0x0f}));

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint8_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(decoded_unsigned.value(), 15u);
    }

    // char 15
    {
        auto const encoding = encode_unsigned(uint8_t{15});
        EXPECT_EQ(encoding, monad::byte_string({0x0f}));

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint8_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(decoded_unsigned.value(), uint8_t{15});
    }

    // integer 1024
    {
        auto const encoding = encode_unsigned(1024u);
        auto const ten_twenty_four_encoding =
            monad::byte_string({0x82, 0x04, 0x00});
        EXPECT_EQ(encoding, ten_twenty_four_encoding);

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint16_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(decoded_unsigned.value(), 1024u);
    }
}

TEST(Rlp_Number, DecodeEncodeBigNumers)
{
    using namespace intx;

    // uint128_t
    {
        auto const encoding =
            encode_unsigned(0xbea34dd04b09ad3b6014251ee2457807_u128);
        auto const sorta_big_num = monad::byte_string(
            {0x90,
             0xbe,
             0xa3,
             0x4d,
             0xd0,
             0x4b,
             0x09,
             0xad,
             0x3b,
             0x60,
             0x14,
             0x25,
             0x1e,
             0xe2,
             0x45,
             0x78,
             0x07});
        EXPECT_EQ(encoding, sorta_big_num);

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint128_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(
            decoded_unsigned.value(), 0xbea34dd04b09ad3b6014251ee2457807_u128);
    }

    // uint256_t
    {
        auto const encoding = encode_unsigned(
            0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_u256);
        auto const big_num = monad::byte_string(
            {0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
             0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd,
             0xa8, 0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
        EXPECT_EQ(encoding, big_num);

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned =
            decode_unsigned<uint256_t>(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(
            decoded_unsigned.value(),
            0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_u256);
    }

    using namespace evmc::literals;
    // bytes32
    {
        auto const encoding = encode_bytes32(
            0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32);
        auto const big_be_num = monad::byte_string(
            {0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
             0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd,
             0xa8, 0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
        EXPECT_EQ(encoding, big_be_num);

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned = decode_bytes32(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(
            decoded_unsigned.value(),
            0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32);
    }

    // address
    {
        auto const encoding =
            encode_address(0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address);
        auto const address = monad::byte_string(
            {0x94, 0xf8, 0x63, 0x63, 0x77, 0xb7, 0xa9, 0x98, 0xb5, 0x1a, 0x3c,
             0xf2, 0xbd, 0x71, 0x1b, 0x87, 0x0b, 0x3a, 0xb0, 0xad, 0x56});
        EXPECT_EQ(encoding, address);

        byte_string_view encoded_unsigned_view{encoding};
        auto const decoded_unsigned = decode_address(encoded_unsigned_view);
        ASSERT_FALSE(decoded_unsigned.has_error());
        EXPECT_EQ(encoded_unsigned_view.size(), 0);

        EXPECT_EQ(
            decoded_unsigned.value(),
            0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address);
    }
}

TEST(Rlp_Number, EncodeCombinations)
{
    // the integer list of 0 and 9
    auto const encoded_comb1 =
        encode_list2(encode_unsigned(0u), encode_unsigned(9u));
    EXPECT_EQ(encoded_comb1, monad::byte_string({0xC2, 0x80, 0x09}));

    // encoding list that is larger than 55 bytes
    auto const *const fifty_six_char_string =
        "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
    auto const fifty_six_char_string_encoding = monad::byte_string(
        {0xb8, 0x38, 'L', 'o', 'r', 'e', 'm', ' ', 'i', 'p', 's', 'u',
         'm',  ' ',  'd', 'o', 'l', 'o', 'r', ' ', 's', 'i', 't', ' ',
         'a',  'm',  'e', 't', ',', ' ', 'c', 'o', 'n', 's', 'e', 'c',
         't',  'e',  't', 'u', 'r', ' ', 'a', 'd', 'i', 'p', 'i', 's',
         'i',  'c',  'i', 'n', 'g', ' ', 'e', 'l', 'i', 't'});
    auto const encoded_comb2 = encode_list2(
        encode_string2(to_byte_string_view(fifty_six_char_string)));
    auto const expected_list_encoding =
        monad::byte_string({0xf7 + 1, 58}) + fifty_six_char_string_encoding;
    EXPECT_EQ(encoded_comb2, expected_list_encoding);
}
