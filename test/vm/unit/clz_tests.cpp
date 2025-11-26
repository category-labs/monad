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

#include "evm_fixture.hpp"

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

using monad::EvmTraits;
using namespace monad::vm;
using namespace monad::vm::compiler;
using namespace monad::vm::compiler::test;

// Test cases from EIP-7939
// See: https://eips.ethereum.org/EIPS/eip-7939

// Test Case 1: CLZ(0x0) == 256
TYPED_TEST(VMTraitsTest, CLZ_Zero)
{
    // PUSH32 0x0, CLZ, STOP
    // Expected: stack[0] = 256 (0x100)
    TestFixture::execute(10, {PUSH32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        // Gas: 3 (PUSH32) + 5 (CLZ) = 8, remaining = 2
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        // CLZ not supported before Osaka
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

// Test Case 2: CLZ(0x8000...0) == 0
TYPED_TEST(VMTraitsTest, CLZ_MostSignificantBitSet)
{
    // PUSH32
    // 0x8000000000000000000000000000000000000000000000000000000000000000, CLZ,
    // STOP Expected: stack[0] = 0
    TestFixture::execute(10, {PUSH32, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

// Test Case 3: CLZ(0xFFFF...FF) == 0
TYPED_TEST(VMTraitsTest, CLZ_AllBitsSet)
{
    // PUSH32
    // 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, CLZ,
    // STOP Expected: stack[0] = 0
    TestFixture::execute(10, {PUSH32, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

// Test Case 4: CLZ(0x4000...0) == 1
TYPED_TEST(VMTraitsTest, CLZ_Bit254Set)
{
    // PUSH32
    // 0x4000000000000000000000000000000000000000000000000000000000000000, CLZ,
    // STOP Expected: stack[0] = 1
    TestFixture::execute(10, {PUSH32, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

// Test Case 5: CLZ(0x7FFF...FF) == 1
TYPED_TEST(VMTraitsTest, CLZ_Bit254SetAllLowerBitsSet)
{
    // PUSH32
    // 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, CLZ,
    // STOP Expected: stack[0] = 1
    TestFixture::execute(10, {PUSH32, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                              0xFF,   0xFF, 0xFF, 0xFF, 0xFF, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

// Test Case 6: CLZ(0x1) == 255
TYPED_TEST(VMTraitsTest, CLZ_LeastSignificantBitSet)
{
    // PUSH32
    // 0x0000000000000000000000000000000000000000000000000000000000000001, CLZ,
    // STOP Expected: stack[0] = 255 (0xFF)
    TestFixture::execute(10, {PUSH32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                              0x00,   0x00, 0x00, 0x00, 0x01, CLZ,  STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 2);
    }
    else {
        ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
    }
}

TYPED_TEST(VMTraitsTest, CLZ_StackUnderflow)
{
    // CLZ without any value on stack should fail
    TestFixture::execute(10, {CLZ, STOP});

    ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
}

TYPED_TEST(VMTraitsTest, CLZ_GasCost)
{
    // CLZ should cost 5 gas (same as MUL per EIP-7939)
    // PUSH1 0x01, CLZ, STOP
    TestFixture::execute(10, {PUSH1, 0x01, CLZ, STOP});

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_OSAKA) {
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        // Gas consumed: 3 (PUSH1) + 5 (CLZ) = 8
        // Gas left: 10 - 8 = 2
        ASSERT_EQ(this->result_.gas_left, 2);
    }
}
