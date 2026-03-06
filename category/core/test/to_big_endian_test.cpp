// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <gtest/gtest.h>

#include <category/core/int.hpp>

#include <array>
#include <cstdint>
#include <cstring>

using namespace monad;

namespace
{

    template <typename T>
    std::array<uint8_t, sizeof(T)> read_bytes(T const &x)
    {
        std::array<uint8_t, sizeof(T)> result;
        std::memcpy(result.data(), &x, sizeof(T));
        return result;
    }

    TEST(ToBigEndian, uint8)
    {
        // Single byte: no-op
        EXPECT_EQ(monad::to_big_endian(uint8_t{0x00}), uint8_t{0x00});
        EXPECT_EQ(monad::to_big_endian(uint8_t{0x42}), uint8_t{0x42});
        EXPECT_EQ(monad::to_big_endian(uint8_t{0xff}), uint8_t{0xff});
    }

    TEST(ToBigEndian, uint16)
    {
        // 0x0102 in native (LE) memory is [02 01]
        // to_big_endian should produce bytes [01 02] in memory
        EXPECT_EQ(
            read_bytes(monad::to_big_endian(uint16_t{0x0102})),
            (std::array<uint8_t, 2>{0x01, 0x02}));
        EXPECT_EQ(
            read_bytes(monad::to_big_endian(uint16_t{0xabcd})),
            (std::array<uint8_t, 2>{0xab, 0xcd}));
    }

    TEST(ToBigEndian, uint32)
    {
        EXPECT_EQ(
            read_bytes(monad::to_big_endian(uint32_t{0x01020304})),
            (std::array<uint8_t, 4>{0x01, 0x02, 0x03, 0x04}));
        EXPECT_EQ(
            read_bytes(monad::to_big_endian(uint32_t{0xdeadbeef})),
            (std::array<uint8_t, 4>{0xde, 0xad, 0xbe, 0xef}));
    }

    TEST(ToBigEndian, uint64)
    {
        EXPECT_EQ(
            read_bytes(monad::to_big_endian(uint64_t{0x0102030405060708ULL})),
            (std::array<uint8_t, 8>{
                0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08}));
    }

    TEST(ToBigEndian, uint128)
    {
        uint128_t const value =
            (uint128_t{0x0102030405060708ULL} << 64) | 0x090a0b0c0d0e0f10ULL;

        EXPECT_EQ(
            read_bytes(monad::to_big_endian(value)),
            (std::array<uint8_t, 16>{
                0x01,
                0x02,
                0x03,
                0x04,
                0x05,
                0x06,
                0x07,
                0x08,
                0x09,
                0x0a,
                0x0b,
                0x0c,
                0x0d,
                0x0e,
                0x0f,
                0x10}));
    }

    TEST(ToBigEndian, uint256)
    {
        uint256_t const value = (uint256_t{0x0102030405060708ULL} << 192) |
                                (uint256_t{0x090a0b0c0d0e0f10ULL} << 128) |
                                (uint256_t{0x1112131415161718ULL} << 64) |
                                uint256_t{0x191a1b1c1d1e1f20ULL};

        EXPECT_EQ(
            read_bytes(monad::to_big_endian(value)),
            (std::array<uint8_t, 32>{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                                     0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
                                     0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
                                     0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
                                     0x1d, 0x1e, 0x1f, 0x20}));
    }

    TEST(ToBigEndian, uint512)
    {
        uint512_t const value = (uint512_t{0x0102030405060708ULL} << 448) |
                                (uint512_t{0x090a0b0c0d0e0f10ULL} << 384) |
                                (uint512_t{0x1112131415161718ULL} << 320) |
                                (uint512_t{0x191a1b1c1d1e1f20ULL} << 256) |
                                (uint512_t{0x2122232425262728ULL} << 192) |
                                (uint512_t{0x292a2b2c2d2e2f30ULL} << 128) |
                                (uint512_t{0x3132333435363738ULL} << 64) |
                                uint512_t{0x393a3b3c3d3e3f40ULL};

        EXPECT_EQ(
            read_bytes(monad::to_big_endian(value)),
            (std::array<uint8_t, 64>{
                0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
                0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
                0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
                0x1f, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,
                0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32,
                0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c,
                0x3d, 0x3e, 0x3f, 0x40}));
    }

    TEST(ToBigEndian, idempotent)
    {
        // Applying to_big_endian twice returns the original value
        EXPECT_EQ(
            monad::to_big_endian(monad::to_big_endian(uint32_t{0xdeadbeef})),
            uint32_t{0xdeadbeef});
        uint256_t const y{0x0102030405060708ULL};
        EXPECT_EQ(monad::to_big_endian(monad::to_big_endian(y)), y);
    }

    TEST(ToBigEndian, zero)
    {
        EXPECT_EQ(monad::to_big_endian(uint32_t{0}), uint32_t{0});
        EXPECT_EQ(monad::to_big_endian(uint256_t{0}), uint256_t{0});
    }

} // namespace
