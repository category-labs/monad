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

#include "fixture.hpp"

#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/math.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;
using namespace monad::vm::runtime;

TEST_F(RuntimeTest, Mul)
{
    auto f = wrap(mul);

    ASSERT_EQ(f(10, 10), 100);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE_u256,
          0),
        0);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_u256,
          2),
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE_u256);
    ASSERT_EQ(
        f(0xcd566972b5e50104011a92b59fa8e0b1234851ae_u256,
          0x01000000000000000000000000_u256),
        0xcd566972b5e50104011a92b59fa8e0b1234851ae000000000000000000000000_u256);
    ASSERT_EQ(
        f(0x747d1d94b679f91eeeee9ecca05eb0b0a71ea2020c4e94bdb62e4d5f9fef9244_u256,
          0xcd566972b5e50104011a92b59fa8e0b1234851ae_u256),
        0xd4dac120ee7e085767e373530940f800a1d01787793fcf63bcf635fdf13cee38_u256);
}

TEST_F(RuntimeTest, Mul_192)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit192{0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit128{0, static_cast<uint64_t>(1) << 63};
    uint256_t bit64{static_cast<uint64_t>(1) << 63};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {0, 0},
        {0, bit256},
        {0, bit192},
        {0, bit128},
        {bit256, 0},
        {bit192, 0},
        {bit128, 0},
        {1, 1},
        {1, bit256},
        {bit256, 1},
        {1, bit192},
        {bit192, 1},
        {1, bit128},
        {bit128, 1},
        {bit64, -bit64},
        {-bit64, bit64},
        {-bit64, -bit64},
        {bit64, bit256},
        {bit256, bit64},
        {-bit64, bit256},
        {bit256, -bit64},
        {bit64, bit192},
        {bit192, bit64},
        {-bit64, bit192},
        {bit192, -bit64},
        {bit64, bit128},
        {bit128, bit64},
        {-bit64, bit128},
        {bit128, -bit64},
        {5, 6},
        {5, -bit64},
        {-bit64, 5},
        {5, bit64},
        {bit64, 5},
        {0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE_u256,
         2}};

    for (auto const &[a, b] : inputs) {
        uint256_t result;
        monad_vm_runtime_mul_192(&result, &a, &b);
        ASSERT_EQ(result, mulmod(a, b, uint256_t{1} << 192));
    }
}

TEST_F(RuntimeTest, UDiv)
{
    auto f = wrap(udiv);

    ASSERT_EQ(f(4, 2), 2);
    ASSERT_EQ(f(4, 3), 1);
    ASSERT_EQ(f(4, 5), 0);
    ASSERT_EQ(f(4, 0), 0);
    ASSERT_EQ(f(10, 10), 1);
    ASSERT_EQ(f(1, 2), 0);
}

TEST_F(RuntimeTest, SDiv)
{
    constexpr auto neg = [](auto n) { return -uint256_t{n}; };

    auto f = wrap(sdiv);

    ASSERT_EQ(f(8, 2), 4);
    ASSERT_EQ(f(neg(4), 2), neg(2));
    ASSERT_EQ(f(neg(4), neg(2)), 2);
    ASSERT_EQ(f(100, 0), 0);
    ASSERT_EQ(f(neg(4378), 0), 0);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE_u256,
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_u256),
        2);
}

TEST_F(RuntimeTest, UMod)
{
    auto f = wrap(umod);

    ASSERT_EQ(f(10, 3), 1);
    ASSERT_EQ(f(17, 5), 2);
    ASSERT_EQ(f(247893, 0), 0);
    ASSERT_EQ(
        f(0x00000FBFC7A6E43ECE42F633F09556EF460006AE023965495AE1F990468E3B58_u256,
          15),
        4);
}

TEST_F(RuntimeTest, SMod)
{
    auto f = wrap(smod);

    ASSERT_EQ(f(10, 3), 1);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8_u256,
          0),
        0);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8_u256,
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD_u256),
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE_u256);
}

TEST_F(RuntimeTest, AddMod)
{
    auto f = wrap(addmod);

    ASSERT_EQ(f(10, 10, 8), 4);
    ASSERT_EQ(f(134, 378, 0), 0);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_u256,
          2,
          2),
        1);
}

TEST_F(RuntimeTest, MulMod)
{
    auto f = wrap(mulmod);

    ASSERT_EQ(f(10, 10, 8), 4);
    ASSERT_EQ(f(134, 378, 0), 0);
    ASSERT_EQ(
        f(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_u256,
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF_u256,
          12),
        9);
}

TEST_F(RuntimeTest, ExpOld)
{
    auto f = wrap(exp<EvmTraits<EVMC_TANGERINE_WHISTLE>>);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(f(100, 0), 1);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 10;
    ASSERT_EQ(f(10, 2), 100);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 20;
    ASSERT_EQ(
        f(3, 256),
        0xC7ADEEB80D4FFF81FED242815E55BC8375A205DE07597D51D2105F2F0730F401_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 30;
    ASSERT_EQ(
        f(5, 65536),
        0x6170C9D4CF040C5B5B784780A1BD33BA7B6BB3803AA626C24C21067A267C0001_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, ExpNew)
{
    auto f = wrap(exp<EvmTraits<EVMC_CANCUN>>);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(f(100, 0), 1);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 50;
    ASSERT_EQ(f(10, 2), 100);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 100;
    ASSERT_EQ(
        f(3, 256),
        0xC7ADEEB80D4FFF81FED242815E55BC8375A205DE07597D51D2105F2F0730F401_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    ctx_.gas_remaining = 150;
    ASSERT_EQ(
        f(5, 65536),
        0x6170C9D4CF040C5B5B784780A1BD33BA7B6BB3803AA626C24C21067A267C0001_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}
