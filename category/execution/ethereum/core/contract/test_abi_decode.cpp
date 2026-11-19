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

#include <category/core/address.h>
#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes32.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <limits>

#include <gtest/gtest.h>

using namespace monad;

template <typename T>
class UintDecodeTest : public ::testing::Test
{
};

typedef ::testing::Types<u8_be, u16_be, u32_be, u64_be, u256_be> UintTypes;
TYPED_TEST_SUITE(UintDecodeTest, UintTypes);

TYPED_TEST(UintDecodeTest, uint)
{
    TypeParam const expected{255};
    bytes32_t const encoded = abi_encode_uint<TypeParam>(expected);
    byte_string_view input{encoded};
    auto const decoded_res = abi_decode_fixed<TypeParam>(input);
    EXPECT_TRUE(input.empty());
    EXPECT_TRUE(decoded_res.has_value());
    EXPECT_EQ(decoded_res.value().native(), expected);
}

TYPED_TEST(UintDecodeTest, input_too_short)
{
    TypeParam const expected{255};
    bytes32_t const encoded = abi_encode_uint<TypeParam>(expected);
    byte_string_view input = byte_string_view{encoded}.substr(1);
    auto const decoded_res = abi_decode_fixed<TypeParam>(input);
    EXPECT_FALSE(input.empty());
    EXPECT_TRUE(decoded_res.has_error());
    EXPECT_EQ(decoded_res.assume_error(), AbiDecodeError::InputTooShort);
}

TYPED_TEST(UintDecodeTest, uint_higher_bits_ignored)
{
    // Note that everything from uint8 to uint256 is encoded to a bytes32.
    // Now suppose we are decoding a bytes32 into a uint64, and the value
    // inside the bytes32 is a uint256. The top bits are ignored.
    []<class... BigEndianType>() {
        (
            [&] {
                using EncodedNative = typename BigEndianType::native_type;
                using DecodedNative = typename TypeParam::native_type;

                bytes32_t const encoded = abi_encode_uint<BigEndianType>(
                    std::numeric_limits<EncodedNative>::max());
                byte_string_view input{encoded};
                auto const decoded_res = abi_decode_fixed<TypeParam>(input);
                ASSERT_FALSE(decoded_res.has_error());
                if constexpr (
                    std::numeric_limits<EncodedNative>::max() <
                    std::numeric_limits<DecodedNative>::max()) {
                    // it should fit in the type
                    EXPECT_EQ(
                        decoded_res.value().native(),
                        std::numeric_limits<EncodedNative>::max());
                }
                else {
                    // output is truncated to max our type can fit
                    EXPECT_EQ(
                        decoded_res.value().native(),
                        std::numeric_limits<DecodedNative>::max());
                }
            }(),
            ...);
    }.template operator()<u16_be, u32_be, u64_be, u256_be>();
}

TEST(AbiDecode, address)
{
    Address const expected = monad_address{
        0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB,
        0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB};
    bytes32_t const encoded = abi_encode_address(expected);
    byte_string_view input{encoded};
    auto const decoded_res = abi_decode_fixed<Address>(input);
    ASSERT_FALSE(decoded_res.has_error());
    EXPECT_EQ(decoded_res.value(), expected);
}

TEST(AbiDecode, address_higher_bits_ignored)
{
    Address const expected = monad_address{
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
    bytes32_t const encoded = monad_bytes32{
        0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC,
        0xCC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
    byte_string_view input{encoded};
    auto const decoded_res = abi_decode_fixed<Address>(input);
    ASSERT_FALSE(decoded_res.has_error());
    EXPECT_EQ(decoded_res.value(), expected);
}

TEST(AbiDecode, bytes_in_tail_simple)
{
    byte_string_fixed<48> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_bytes_tail<48>(input);
    ASSERT_FALSE(decode_res.has_error());
    EXPECT_EQ(decode_res.value(), bytes);
}

TEST(AbiDecode, bytes_in_tail_input_too_short)
{
    byte_string_fixed<48> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input =
        byte_string_view{encoded}.substr(0, bytes.size() - 5);
    auto const decode_res = abi_decode_bytes_tail<48>(input);
    ASSERT_TRUE(decode_res.has_error());
    EXPECT_EQ(decode_res.assume_error(), AbiDecodeError::InputTooShort);
}

TEST(AbiDecode, bytes_in_tail_length_mismatch)
{
    byte_string_fixed<33> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_bytes_tail<48>(input);
    ASSERT_TRUE(decode_res.has_error());
    EXPECT_EQ(decode_res.assume_error(), AbiDecodeError::LengthMismatch);
}

TEST(AbiDecode, dynamic_bytes_tail_decodes_less_than_word)
{
    byte_string_fixed<8> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_dynamic_bytes_tail<8>(input);
    ASSERT_FALSE(decode_res.has_error());
    EXPECT_TRUE(input.empty());
    EXPECT_EQ(decode_res.value(), bytes);
}

TEST(AbiDecode, dynamic_bytes_tail_decodes_exactly_word)
{
    byte_string_fixed<32> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_dynamic_bytes_tail<32>(input);
    ASSERT_FALSE(decode_res.has_error());
    EXPECT_TRUE(input.empty());
    EXPECT_EQ(decode_res.value(), bytes);
}

TEST(AbiDecode, dynamic_bytes_tail_decodes_more_than_word)
{
    byte_string_fixed<48> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_dynamic_bytes_tail<48>(input);
    ASSERT_FALSE(decode_res.has_error());
    EXPECT_TRUE(input.empty());
    EXPECT_EQ(decode_res.value(), bytes);
}

TEST(AbiDecode, dynamic_bytes_tail_input_too_short)
{
    byte_string_fixed<8> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input = byte_string_view{encoded}.substr(0, 32 + 4);
    auto const decode_res = abi_decode_dynamic_bytes_tail<8>(input);
    ASSERT_TRUE(decode_res.has_error());
    EXPECT_EQ(decode_res.assume_error(), AbiDecodeError::InputTooShort);
}

TEST(AbiDecode, dynamic_bytes_tail_length_mismatch)
{
    byte_string_fixed<8> bytes{};
    bytes.fill(0xAB);
    byte_string const encoded = abi_encode_bytes(to_byte_string_view(bytes));
    byte_string_view input{encoded};
    auto const decode_res = abi_decode_dynamic_bytes_tail<32>(input);
    ASSERT_TRUE(decode_res.has_error());
    EXPECT_EQ(decode_res.assume_error(), AbiDecodeError::LengthMismatch);
}

TEST(AbiDecode, runtime_dynamic_bytes_tail_word_boundaries)
{
    for (size_t const length : {0uz, 1uz, 31uz, 32uz, 33uz, 64uz, 65uz}) {
        SCOPED_TRACE(length);
        byte_string const payload(length, 0xAB);
        byte_string encoded(32, 0);
        encoded.back() = static_cast<unsigned char>(length);
        encoded += payload;
        encoded.append((32 - length % 32) % 32, 0);
        byte_string_view input{encoded};

        auto const decoded = abi_decode_dynamic_bytes_tail(input);
        ASSERT_TRUE(decoded.has_value());
        EXPECT_EQ(decoded.value(), payload);
        EXPECT_EQ(decoded.value().data(), encoded.data() + 32);
        EXPECT_TRUE(input.empty());
    }
}

TEST(AbiDecode, runtime_dynamic_bytes_tail_rejects_truncation)
{
    byte_string encoded(96, 0);
    encoded[31] = 33;
    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        byte_string_view input = byte_string_view{encoded}.substr(0, size);
        auto const decoded = abi_decode_dynamic_bytes_tail(input);
        ASSERT_TRUE(decoded.has_error());
        EXPECT_EQ(decoded.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST(AbiDecode, runtime_dynamic_bytes_tail_rejects_oversized_lengths)
{
    uint256_t const lengths[] = {
        uint256_t{std::numeric_limits<size_t>::max()},
        uint256_t{std::numeric_limits<size_t>::max()} + 1,
        std::numeric_limits<uint256_t>::max()};
    for (auto const length : lengths) {
        bytes32_t const encoded = abi_encode_uint(u256_be{length});
        byte_string_view input{encoded};
        auto const decoded = abi_decode_dynamic_bytes_tail(input);
        ASSERT_TRUE(decoded.has_error());
        EXPECT_EQ(decoded.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST(AbiDecode, runtime_dynamic_bytes_tail_consumes_consecutive_tails)
{
    byte_string const first(33, 0xAB);
    byte_string const second(1, 0xCD);
    byte_string const encoded =
        abi_encode_bytes(first) + abi_encode_bytes(second);
    byte_string_view input{encoded};

    auto const first_decoded = abi_decode_dynamic_bytes_tail(input);
    ASSERT_TRUE(first_decoded.has_value());
    EXPECT_EQ(first_decoded.value(), first);
    EXPECT_EQ(input.size(), 64);

    auto const second_decoded = abi_decode_dynamic_bytes_tail(input);
    ASSERT_TRUE(second_decoded.has_value());
    EXPECT_EQ(second_decoded.value(), second);
    EXPECT_TRUE(input.empty());
}

TEST(AbiDecode, complex_decode)
{
    // encode with both a head and tail. Note that we only decode known types,
    // and all dynamic data will be last in the head

    byte_string_fixed<33> mock_secp_key{};
    mock_secp_key.fill(0xAB);

    byte_string_fixed<48> mock_bls_key{};
    mock_bls_key.fill(0xCD);

    AbiEncoder encoder;
    encoder.add_uint<u64_be>(200);
    encoder.add_uint<u256_be>(50000_u256);
    encoder.add_bytes(to_byte_string_view(mock_secp_key));
    encoder.add_bytes(to_byte_string_view(mock_bls_key));
    auto const encoded = encoder.encode_final();

    // decode head (fixed size data)
    byte_string_view input{encoded};
    {
        // u64
        auto const decode_res = abi_decode_fixed<u64_be>(input);
        ASSERT_FALSE(decode_res.has_error());
        EXPECT_EQ(decode_res.value().native(), 200);
    }
    {
        // u256
        auto const decode_res = abi_decode_fixed<u256_be>(input);
        ASSERT_FALSE(decode_res.has_error());
        EXPECT_EQ(decode_res.value().native(), 50000_u256);
    }
    {
        // secp tail offset - ignore
        auto const decode_res = abi_decode_fixed<u256_be>(input);
        ASSERT_FALSE(decode_res.has_error());
    }
    {
        // bls tail offset - ignore
        auto const decode_res = abi_decode_fixed<u256_be>(input);
        ASSERT_FALSE(decode_res.has_error());
    }

    // decode tail (dynamic data)
    {
        // mock secp key
        auto const decode_res = abi_decode_bytes_tail<33>(input);
        ASSERT_FALSE(decode_res.has_error());
        EXPECT_EQ(decode_res.value(), mock_secp_key);
    }
    {
        // mock bls key
        auto const decode_res = abi_decode_bytes_tail<48>(input);
        ASSERT_FALSE(decode_res.has_error());
        EXPECT_EQ(decode_res.value(), mock_bls_key);
    }
}
