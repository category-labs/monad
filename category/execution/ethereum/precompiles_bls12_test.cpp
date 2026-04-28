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

#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

using namespace monad;

namespace
{
    // Build a 64-byte input buffer from 16 zero-padding bytes + 48 field bytes.
    std::array<uint8_t, 64> make_fp_input(uint8_t const (&fp)[48])
    {
        std::array<uint8_t, 64> buf{};
        std::memcpy(buf.data() + 16, fp, 48);
        return buf;
    }
} // namespace

TEST(BLS12ReadFp, AcceptsZero)
{
    // Zero is a valid field element (< p).
    std::array<uint8_t, 64> const input{};
    EXPECT_TRUE(bls12::read_fp(input.data()).has_value());
}

TEST(BLS12ReadFp, AcceptsModulusMinusOne)
{
    // p - 1 is the largest valid field element.
    // p ends in ...aaab, so p-1 ends in ...aaaa.
    auto fp = bls12::BASE_FIELD_MODULUS;
    // Decrement the last byte (no borrow since last byte is 0xab > 0).
    fp.bytes[47] -= 1;
    auto const input = make_fp_input(fp.bytes);
    EXPECT_TRUE(bls12::read_fp(input.data()).has_value());
}

TEST(BLS12ReadFp, RejectsModulus)
{
    // p itself is not a valid field element.
    auto const input = make_fp_input(bls12::BASE_FIELD_MODULUS.bytes);
    EXPECT_FALSE(bls12::read_fp(input.data()).has_value());
}

TEST(BLS12ReadFp, RejectsModulusPlusOne)
{
    // p + 1 is also invalid.
    auto fp = bls12::BASE_FIELD_MODULUS;
    fp.bytes[47] += 1; // no carry; last byte is 0xab, +1 = 0xac
    auto const input = make_fp_input(fp.bytes);
    EXPECT_FALSE(bls12::read_fp(input.data()).has_value());
}

TEST(BLS12ReadFp, RejectsNonZeroPaddingBytes)
{
    // The 16 leading bytes must be zero; a non-zero byte there means the value
    // is >= 2^384, which is > p, so it must be rejected.
    std::array<uint8_t, 64> input{};
    input[0] = 0x01; // set first padding byte non-zero
    EXPECT_FALSE(bls12::read_fp(input.data()).has_value());
}
