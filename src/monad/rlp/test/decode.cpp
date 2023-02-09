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
    auto test_single = [](byte_string_loc val, monad::byte_string enc)
    {
        EXPECT_EQ(val, decode_length(enc, 0, enc.size()));
    };
    test_single(0, monad::byte_string({0x00}));
    test_single(15, monad::byte_string({0x0f}));
    test_single(122, monad::byte_string({0x7a}));
    test_single(1024, monad::byte_string({0x04, 0x00}));
    test_single(772, monad::byte_string({0x03, 0x04}));
    test_single(553, monad::byte_string({0x02, 0x29}));
    test_single(1176, monad::byte_string({0x04, 0x98}));
    test_single(16706, monad::byte_string({0x41, 0x42}));
    test_single(31530, monad::byte_string({0x7b, 0x2a}));
    test_single(65535, monad::byte_string({0xff, 0xff}));
}

TEST(Rlp, DecodeAfterEncodeString)
{
    auto test_single = [](std::string s) {
        auto enc = to_byte_string_view(s);
        EXPECT_EQ(decode_string(encode_string(enc)), enc);
    };
    test_single("hello world");
    test_single("Lorem ipsum dolor sit amet, consectetur adipisicing elit");
    test_single("monad");
    test_single("Monad Labs");
}

// Need to have function signiture defined the 'decode.hpp'

// TEST(Rlp, DecodeAfterEncodeList)
// {
//    // Empty list
//     auto encoding = encode_list();
//     auto decoding = decode_list(encoding)
//     EXPECT_EQ(encoding, monad::byte_string({0xc0}));

//     // list of two strings
//     encoding = encode_list(
//         encode_string(to_byte_string_view("cat")),
//         encode_string(to_byte_string_view("dog")));
//     EXPECT_EQ(
//         encoding,
//         monad::byte_string({0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g'}));
// }