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

#include "evm_fixture.hpp"

#include <category/vm/evm/opcodes.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>

using namespace monad::vm::compiler;
using namespace monad::vm::test;

TYPED_TEST(VMTraitsTest, ExtensionInvalidSelector)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (uint8_t const selector :
         std::array<uint8_t, 5>{0x02, 0x5B, 0x60, 0x7F, 0xFF}) {
        for (auto const impl : impls) {
            TestFixture::execute(100'000, {EXTENSION, selector}, {}, impl);
            ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
            ASSERT_EQ(this->result_.gas_left, 0);
        }
    }
}

TYPED_TEST(VMTraitsTest, ExtensionJumpdestAnalysis)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (auto const impl : impls) {
        TestFixture::execute(
            100'000, {PUSH1, 4, JUMP, EXTENSION, JUMPDEST, STOP}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);

        TestFixture::execute(
            100'000,
            {PUSH1, 5, JUMP, EXTENSION, PUSH1, JUMPDEST, STOP},
            {},
            impl);
        ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
    }
}

TYPED_TEST(VMTraitsTest, ExtensionAtEndOfCode)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (auto const impl : impls) {
        TestFixture::execute(100'000, {EXTENSION}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
        ASSERT_EQ(this->result_.gas_left, 0);

        TestFixture::execute(100'000, {PUSH0, EXTENSION}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
        ASSERT_EQ(this->result_.gas_left, 0);
    }
}
