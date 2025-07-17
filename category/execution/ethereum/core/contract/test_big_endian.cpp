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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <gtest/gtest.h>

#include <limits>

using namespace monad;

TEST(BigEndian, u16)
{
    uint16_t const native_u16 = std::numeric_limits<uint16_t>::max();
    uint16_t const be_u16 = __builtin_bswap16(native_u16);
    u16_be const be_u16_type = native_u16;
    EXPECT_EQ(0, std::memcmp(&be_u16, &be_u16_type, sizeof(uint16_t)));
    EXPECT_EQ(native_u16, be_u16_type.native());
}

TEST(BigEndian, u32)
{
    uint32_t const native_u32 = std::numeric_limits<uint32_t>::max();
    uint32_t const be_u32 = __builtin_bswap32(native_u32);
    u32_be const be_u32_type = native_u32;
    EXPECT_EQ(0, std::memcmp(&be_u32, &be_u32_type, sizeof(uint32_t)));
    EXPECT_EQ(native_u32, be_u32_type.native());
}

TEST(BigEndian, u64)
{
    uint64_t const native_u64 = std::numeric_limits<uint64_t>::max();
    uint64_t const be_u64 = __builtin_bswap64(native_u64);
    u64_be const be_u64_type = native_u64;
    EXPECT_EQ(0, std::memcmp(&be_u64, &be_u64_type, sizeof(uint64_t)));
    EXPECT_EQ(native_u64, be_u64_type.native());
}

TEST(BigEndian, uint256)
{
    uint256_t const native_u256 = std::numeric_limits<uint256_t>::max();
    bytes32_t const be_u256 = intx::be::store<bytes32_t>(native_u256);
    u256_be const be_u256_type = native_u256;
    EXPECT_EQ(0, std::memcmp(&be_u256, &be_u256_type, sizeof(uint256_t)));
    EXPECT_EQ(native_u256, be_u256_type.native());
}