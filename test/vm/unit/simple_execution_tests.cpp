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

#include <vm/vm.h>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad::vm::testing;

TEST(SimpleExecutionTests, Stop)
{
    auto contract = standalone_evm_jit("00");
    contract();

    ASSERT_EQ(contract.stack_pointer(), 0);
}

TEST(SimpleExecutionTests, Push0)
{
    auto contract = standalone_evm_jit("5F00");
    contract();

    ASSERT_EQ(contract.stack_pointer(), 1);
    ASSERT_EQ(contract.stack(0), 0);
}

TEST(SimpleExecutionTests, Push1)
{
    auto contract = standalone_evm_jit("600100");
    contract();

    ASSERT_EQ(contract.stack_pointer(), 1);
    ASSERT_EQ(contract.stack(0), 1);
}

TEST(SimpleExecutionTests, MultiplePushes)
{
    auto contract = standalone_evm_jit("5F60116122226233333300");
    contract();

    ASSERT_EQ(contract.stack_pointer(), 4);
    ASSERT_EQ(contract.stack(0), 0);
    ASSERT_EQ(contract.stack(1), 0x11);
    ASSERT_EQ(contract.stack(2), 0x2222);
    ASSERT_EQ(contract.stack(3), 0x333333);
}

TEST(SimpleExecutionTests, Push32)
{
    using namespace intx;

    auto contract = standalone_evm_jit(
        "7F323232323232323232323232323232323232323232323232323232323232323200");
    contract();

    ASSERT_EQ(contract.stack_pointer(), 1);
    ASSERT_EQ(
        contract.stack(0),
        0x3232323232323232323232323232323232323232323232323232323232323232_u256);
}

TEST(SimpleExecutionTests, TwoPrograms)
{
    auto contract_a = standalone_evm_jit("631234567863FEDCAB9800");
    auto contract_b = standalone_evm_jit("5F00");

    contract_a();
    contract_b();

    ASSERT_EQ(contract_a.stack_pointer(), 2);
    ASSERT_EQ(contract_b.stack_pointer(), 1);

    ASSERT_EQ(contract_a.stack(0), 0x12345678);
    ASSERT_EQ(contract_a.stack(1), 0xFEDCAB98);
    ASSERT_EQ(contract_b.stack(0), 0);
}
