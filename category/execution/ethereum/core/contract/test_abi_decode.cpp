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
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <limits>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace monad;
using namespace intx::literals;

template <typename T>
class UintDecodeTest : public ::testing::Test
{
};

typedef ::testing::Types<u8_be, u16_be, u32_be, u64_be, u256_be> UintTypes;
TYPED_TEST_SUITE(UintDecodeTest, UintTypes);

TYPED_TEST(UintDecodeTest, uint)
{
    TypeParam expected{255};
    bytes32_t const encoded = abi_encode_uint<TypeParam>(expected);
    byte_string_view input{encoded};
    auto const decoded_res = abi_decode_fixed<TypeParam>(input);
    EXPECT_TRUE(input.empty());
    EXPECT_TRUE(decoded_res.has_value());
    EXPECT_EQ(decoded_res.value().native(), expected);
}

TYPED_TEST(UintDecodeTest, input_too_short)
{
    TypeParam expected{255};
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
    Address expected{{0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA,
                      0xBB, 0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB,
                      0xAA, 0xBB, 0xAA, 0xBB, 0xAA, 0xBB}};
    bytes32_t const encoded = abi_encode_address(expected);
    byte_string_view input{encoded};
    auto const decoded_res = abi_decode_fixed<Address>(input);
    ASSERT_FALSE(decoded_res.has_error());
    EXPECT_EQ(decoded_res.value(), expected);
}

TEST(AbiDecode, address_higher_bits_ignored)
{
    Address expected{{0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}};
    bytes32_t encoded{{0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC,
                       0xCC, 0xCC, 0xCC, 0xCC, 0xFF, 0xFF, 0xFF, 0xFF,
                       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}};
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
