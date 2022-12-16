#include "intx/intx.hpp"
#include <gtest/gtest.h>
#include <monad/rlp/rlp.hpp>

using namespace monad::rlp;

TEST(Rlp, ToBigEndianCompacted)
{
    auto bytes_1 = impl::to_big_endian_compacted(uint16_t{1024});
    auto bytes_2 = impl::to_big_endian_compacted(unsigned{1024});
    auto bytes_3 = impl::to_big_endian_compacted(uint64_t{1024});

    EXPECT_EQ(bytes_1, monad::byte_string({0x04, 0x00}));
    EXPECT_EQ(bytes_1, bytes_2);
    EXPECT_EQ(bytes_2, bytes_3);
}

TEST(Rlp, EncodeSanity)
{
    // Empty list
    auto encoding = encode();
    EXPECT_EQ(encoding, Encoding{monad::byte_string({0xc0})});

    // simple string
    encoding = encode("dog");
    EXPECT_EQ(encoding.bytes.size(), 4);
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x83, 'd', 'o', 'g'}));

    // list of two strings
    encoding = encode("cat", "dog");
    EXPECT_EQ(encoding.bytes, monad::byte_string({ 0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g' }));

    // empty string
    encoding = encode("");
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x80}));

    // the integer 0
    encoding = encode(unsigned{0});
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x80}));

    // the encoded integer 0
    encoding = encode(monad::byte_string({0x00}));
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x00}));

    encoding = encode(uint8_t{0});
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x00}));

    // the encoded integer 15
    encoding = encode(monad::byte_string({0x0f}));
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x0f}));

    encoding = encode(uint8_t{15});
    EXPECT_EQ(encoding.bytes, monad::byte_string({0x0f}));

    // the encoded integer 1024
    encoding = encode(monad::byte_string({0x04, 0x00}));
    auto const ten_twenty_four_encoding = monad::byte_string({0x82, 0x04, 0x00});
    EXPECT_EQ(encoding.bytes, ten_twenty_four_encoding);

    encoding = encode(unsigned{1024});
    EXPECT_EQ(encoding.bytes, ten_twenty_four_encoding);

    // 56 character string
    auto const fifty_six_char_string =
        "Lorem ipsum dolor sit amet, consectetur adipisicing elit";
    auto const fifty_six_char_string_encoding = monad::byte_string(
            {0xb8, 0x38, 'L', 'o', 'r', 'e',
             'm', ' ', 'i', 'p', 's', 'u', 'm', ' ', 'd', 'o', 'l',
             'o', 'r', ' ', 's', 'i', 't', ' ', 'a', 'm', 'e', 't',
             ',', ' ', 'c', 'o', 'n', 's', 'e', 'c', 't', 'e', 't',
             'u', 'r', ' ', 'a', 'd', 'i', 'p', 'i', 's', 'i', 'c',
             'i', 'n', 'g', ' ', 'e', 'l', 'i', 't'});
    encoding = encode(fifty_six_char_string);
    EXPECT_EQ(encoding.bytes, fifty_six_char_string_encoding);

    // encoding list that is larger than 55 bytes
    encoding = encode(1024u, fifty_six_char_string);
    auto const expected_list_encoding = monad::byte_string({0xf7 + 1, 61})
        + ten_twenty_four_encoding + fifty_six_char_string_encoding;
    EXPECT_EQ(encoding.bytes, expected_list_encoding);
}
