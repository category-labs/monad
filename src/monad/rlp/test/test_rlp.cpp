#include <monad/rlp/encode.hpp>
#include <monad/rlp/encode_helpers.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

byte_string_view to_byte_string_view(std::string const &s)
{
    return {reinterpret_cast<unsigned char const *>(&s[0]), s.size()};
}

TEST(Rlp, ToBigEndianCompacted)
{
    auto bytes_1 = to_big_compact(uint16_t{1024});
    auto bytes_2 = to_big_compact(unsigned{1024});
    auto bytes_3 = to_big_compact(uint64_t{1024});

    EXPECT_EQ(bytes_1, monad::byte_string({0x04, 0x00}));
    EXPECT_EQ(bytes_1, bytes_2);
    EXPECT_EQ(bytes_2, bytes_3);
}

TEST(Rlp, EncodeSanity)
{
    // Empty list
    auto encoding = encode_list();
    EXPECT_EQ(encoding, monad::byte_string({0xc0}));

    // simple string
    encoding = encode_string(to_byte_string_view("dog"));
    EXPECT_EQ(encoding.size(), 4);
    EXPECT_EQ(encoding, monad::byte_string({0x83, 'd', 'o', 'g'}));

    // list of two strings
    encoding = encode_list(
        encode_string(to_byte_string_view("cat")),
        encode_string(to_byte_string_view("dog")));
    EXPECT_EQ(
        encoding,
        monad::byte_string({0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g'}));

    // empty string
    encoding = encode_string(to_byte_string_view(""));
    EXPECT_EQ(encoding, monad::byte_string({0x80}));

    // integer 0
    encoding = encode_unsigned(0u);
    EXPECT_EQ(encoding, monad::byte_string({0x80}));

    // string with one char
    encoding = encode_string(monad::byte_string({0x00}));
    EXPECT_EQ(encoding, monad::byte_string({0x00}));

    // char 0
    encoding = encode_unsigned(uint8_t{0});
    EXPECT_EQ(encoding, monad::byte_string({0x80}));

    // integer 15
    encoding = encode_unsigned(15u);
    EXPECT_EQ(encoding, monad::byte_string({0x0f}));

    // char 15
    encoding = encode_unsigned(uint8_t{15});
    EXPECT_EQ(encoding, monad::byte_string({0x0f}));

    // integer 1024
    encoding = encode_unsigned(1024u);
    auto const ten_twenty_four_encoding =
        monad::byte_string({0x82, 0x04, 0x00});
    EXPECT_EQ(encoding, ten_twenty_four_encoding);

    // the integer list of 0 and 9
    encoding = encode_list(encode_unsigned(0u), encode_unsigned(9u));
    EXPECT_EQ(encoding, monad::byte_string({0xC2, 0x80, 0x09}));

    // 56 character string
    auto const fifty_six_char_string =
        "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
    auto const fifty_six_char_string_encoding = monad::byte_string(
        {0xb8, 0x38, 'L', 'o', 'r', 'e', 'm', ' ', 'i', 'p', 's', 'u',
         'm',  ' ',  'd', 'o', 'l', 'o', 'r', ' ', 's', 'i', 't', ' ',
         'a',  'm',  'e', 't', ',', ' ', 'c', 'o', 'n', 's', 'e', 'c',
         't',  'e',  't', 'u', 'r', ' ', 'a', 'd', 'i', 'p', 'i', 's',
         'i',  'c',  'i', 'n', 'g', ' ', 'e', 'l', 'i', 't'});
    encoding = encode_string(to_byte_string_view(fifty_six_char_string));
    EXPECT_EQ(encoding, fifty_six_char_string_encoding);

    // encoding list that is larger than 55 bytes
    encoding = encode_list(
        encode_unsigned(1024u),
        encode_string(to_byte_string_view(fifty_six_char_string)));
    auto const expected_list_encoding = monad::byte_string({0xf7 + 1, 61}) +
                                        ten_twenty_four_encoding +
                                        fifty_six_char_string_encoding;
    EXPECT_EQ(encoding, expected_list_encoding);

    using namespace intx;
    encoding = encode_unsigned(0xbea34dd04b09ad3b6014251ee2457807_u128);
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

    encoding = encode_unsigned(
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_u256);
    auto const big_num = monad::byte_string(
        {0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
         0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd,
         0xa8, 0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
    EXPECT_EQ(encoding, big_num);

    using namespace evmc::literals;
    encoding = encode_bytes32(
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32);
    auto const big_be_num = monad::byte_string(
        {0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
         0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd,
         0xa8, 0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
    EXPECT_EQ(encoding, big_be_num);

    encoding =
        encode_address(0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address);
    auto const address = monad::byte_string(
        {0x94, 0xf8, 0x63, 0x63, 0x77, 0xb7, 0xa9, 0x98, 0xb5, 0x1a, 0x3c,
         0xf2, 0xbd, 0x71, 0x1b, 0x87, 0x0b, 0x3a, 0xb0, 0xad, 0x56});
    EXPECT_EQ(encoding, address);
}

TEST(Rlp, EncodeAccessList)
{
    monad::Transaction::AccessList a{};
    auto encoding = encode_access_list(a);
    auto const empty_access_list = monad::byte_string({0xc0});
    EXPECT_EQ(encoding, empty_access_list);

    monad::Transaction::AccessList b{
        {0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address,
         {0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32}}};
    encoding = encode_access_list(b);
    auto const access_list = monad::byte_string(
        {0xf8, 0x38, 0xf7, 0x94, 0xf8, 0x63, 0x63, 0x77, 0xb7, 0xa9, 0x98, 0xb5,
         0x1a, 0x3c, 0xf2, 0xbd, 0x71, 0x1b, 0x87, 0x0b, 0x3a, 0xb0, 0xad, 0x56,
         0xe1, 0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
         0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd, 0xa8,
         0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
    EXPECT_EQ(encoding, access_list);

    static constexpr auto access_addr{
        0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0_address};
    static constexpr auto key1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr auto key2{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    static const monad::Transaction::AccessList list{
        Transaction::AccessEntry{access_addr, {key1, key2}}};
    auto const eip2930_example = monad::byte_string(
        {0xf8, 0x5b, 0xf8, 0x59, 0x94, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
         0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
         0xa0, 0xf8, 0x42, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07,
         0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03});

    encoding = encode_access_list(list);
    EXPECT_EQ(encoding, eip2930_example);
}
