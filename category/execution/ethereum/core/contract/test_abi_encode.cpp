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
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace monad;
using namespace intx::literals;

TEST(AbiEncode, boolean)
{
    constexpr auto expected_false =
        evmc::from_hex<bytes32_t>(
            "0000000000000000000000000000000000000000000000000000000000000000")
            .value();
    constexpr auto expected_true =
        evmc::from_hex<bytes32_t>(
            "0000000000000000000000000000000000000000000000000000000000000001")
            .value();
    constexpr auto abi_true = abi_encode_bool(true);
    constexpr auto abi_false = abi_encode_bool(false);
    EXPECT_EQ(abi_true, expected_true);
    EXPECT_EQ(abi_false, expected_false);
}

TEST(AbiEncode, u16)
{
    constexpr u16_be input{65535};
    constexpr auto expected =
        evmc::from_hex<bytes32_t>(
            "000000000000000000000000000000000000000000000000000000000000ffff")
            .value();
    constexpr auto actual = abi_encode_uint(input);
    EXPECT_EQ(actual, expected);
}

TEST(AbiEncode, u256)
{
    constexpr u256_be input{15355346523654236542356453_u256};
    constexpr auto expected =
        evmc::from_hex<bytes32_t>(
            "0x0000000000000000000000000000000000000000000cb3"
            "9f00c54ee156444be5")
            .value();
    constexpr auto actual = abi_encode_uint(input);
    EXPECT_EQ(actual, expected);
}

TEST(AbiEncode, address)
{
    constexpr Address input{0xDEADBEEF000000000000000000F00D0000000100_address};
    constexpr auto expected =
        evmc::from_hex<bytes32_t>(
            "000000000000000000000000deadbeef000000000000000000f00d0000000100")
            .value();
    constexpr auto actual = abi_encode_address(input);
    EXPECT_EQ(actual, expected);
}

TEST(AbiEncode, bytes)
{
    byte_string const bls_pubkey =
        evmc::from_hex("0x85686279cefd8ce0d32338910d476ca090b67"
                       "f97fc6f2fbc7d96b0cf3d7dca2fe9"
                       "80de55a715702f2ad35ee5f9bd6f9b")
            .value();
    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000003085"
            "686279cefd8ce0d32338910d476ca090b67f97fc6f2fbc7d96b0cf3d7dca2fe980"
            "de55a715702f2ad35ee5f9bd6f9b00000000000000000000000000000000")
            .value();

    byte_string const output = abi_encode_bytes(bls_pubkey);
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, tuple)
{
    byte_string const input_bytes =
        evmc::from_hex(
            "0x85686279cefd8ce0d32338910d476ca090b67245034520354205420354203542"
            "f97fc6f2fbc7d96b0cf3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb")
            .value();
    u256_be const input_u256 = 15324315423000000_u256;

    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000008000"
            "0000000000000000000000000000000000000000000000003671623936c5c00000"
            "0000000000000000000000000000000000000000000000000000000000e0000000"
            "000000000000000000000000000000000000000000003671623936c5c000000000"
            "0000000000000000000000000000000000000000000000000000003d85686279ce"
            "fd8ce0d32338910d476ca090b67245034520354205420354203542f97fc6f2fbc7"
            "d96b0cf3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb00000000000000000000"
            "0000000000000000000000000000000000000000000000003d85686279cefd8ce0"
            "d32338910d476ca090b67245034520354205420354203542f97fc6f2fbc7d96b0c"
            "f3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb000000")
            .value();
    AbiEncoder encoder;
    encoder.add_bytes(input_bytes);
    encoder.add_uint(input_u256);
    encoder.add_bytes(input_bytes);
    encoder.add_uint(input_u256);
    auto const output = encoder.encode_final();
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, empty_array)
{
    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000002000"
            "00000000000000000000000000000000000000000000000000000000000000")
            .value();
    std::vector<u64_be> arr{};
    AbiEncoder encoder;
    encoder.add_uint_array(arr);
    auto const output = encoder.encode_final();
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, array_tuple)
{
    std::vector<u64_be> arr{2, 4, 20'000, 40'000};

    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000100"
            "000000000000000000000000000000000000000000000000000000000000400000"
            "000000000000000000000000000000000000000000000000000000000004000000"
            "000000000000000000000000000000000000000000000000000000000200000000"
            "000000000000000000000000000000000000000000000000000000040000000000"
            "000000000000000000000000000000000000000000000000004e20000000000000"
            "0000000000000000000000000000000000000000000000009c40")
            .value();
    AbiEncoder encoder;
    encoder.add_bool(true);
    encoder.add_uint_array(arr);
    auto const output = encoder.encode_final();
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, array_address)
{
    std::vector<Address> arr{
        0x1111111111111111111111111111111111111111_address,
        0x2222222222222222222222222222222222222222_address,
        0x3333333333333333333333333333333333333333_address,
        0x4444444444444444444444444444444444444444_address,
    };

    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000002000"
            "000000000000000000000000000000000000000000000000000000000000040000"
            "000000000000000000001111111111111111111111111111111111111111000000"
            "000000000000000000222222222222222222222222222222222222222200000000"
            "000000000000000033333333333333333333333333333333333333330000000000"
            "000000000000004444444444444444444444444444444444444444")
            .value();
    AbiEncoder encoder;
    encoder.add_address_array(arr);
    auto const output = encoder.encode_final();
    EXPECT_EQ(output, expected);
}
