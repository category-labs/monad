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
#include <intx/intx.hpp>

#include <limits>

using namespace monad;

template <typename T>
class BigEndianEncodeTest : public ::testing::Test
{
};

typedef ::testing::Types<uint16_t, uint32_t, uint64_t, uint256_t> UintTypes;
TYPED_TEST_SUITE(BigEndianEncodeTest, UintTypes);

TYPED_TEST(BigEndianEncodeTest, uint_max)
{
    using NativeType = TypeParam;
    using BigEndianType = BigEndian<NativeType>;

    constexpr NativeType native = std::numeric_limits<NativeType>::max();
    constexpr NativeType manual_be_conversion = intx::bswap(native);

    static_assert(sizeof(BigEndianType) == sizeof(NativeType));
    constexpr BigEndianType be_wrapper = native;

    // big endian types have same in memory representation:
    //  * constexpr and runtime
    static_assert(
        be_wrapper == std::bit_cast<BigEndianType>(manual_be_conversion));
    EXPECT_EQ(
        0, std::memcmp(&be_wrapper, &manual_be_conversion, sizeof(TypeParam)));

    // little endian types are equal
    EXPECT_EQ(be_wrapper.native(), native);
}
