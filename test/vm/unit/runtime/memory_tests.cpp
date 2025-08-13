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

#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <algorithm>
#include <cstdint>

using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

TEST_F(RuntimeTest, EmptyMemory)
{
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.memory.cost, 0);
}

TEST_F(RuntimeTest, MStore)
{
    ctx_.gas_remaining = 6;
    call(mstore, 0, 0xFF);
    ASSERT_EQ(ctx_.memory.size, 32);
    ASSERT_EQ(ctx_.memory.data[31], 0xFF);
    ASSERT_EQ(ctx_.memory.cost, 3);
    ASSERT_EQ(ctx_.gas_remaining, 3);

    call(mstore, 1, 0xFF);
    ASSERT_EQ(ctx_.memory.size, 64);
    ASSERT_EQ(ctx_.memory.data[31], 0x00);
    ASSERT_EQ(ctx_.memory.data[32], 0xFF);
    ASSERT_EQ(ctx_.memory.cost, 6);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, MStoreWord)
{
    ctx_.gas_remaining = 3;
    call(
        mstore,
        0,
        0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F_u256);

    ASSERT_EQ(ctx_.memory.size, 32);
    ASSERT_EQ(ctx_.memory.cost, 3);
    ASSERT_EQ(ctx_.gas_remaining, 0);

    for (auto i = 0u; i < 31; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i);
    }
}

TEST_F(RuntimeTest, MCopy)
{
    ctx_.gas_remaining = 20;

    call(mstore8, 1, 1);
    call(mstore8, 2, 2);
    call(mcopy, 3, 1, 33);

    ASSERT_EQ(ctx_.memory.cost, 6);
    ASSERT_EQ(ctx_.gas_remaining, 8);
    ASSERT_EQ(ctx_.memory.size, 64);
    ASSERT_EQ(ctx_.memory.data[0], 0);
    ASSERT_EQ(ctx_.memory.data[1], 1);
    ASSERT_EQ(ctx_.memory.data[2], 2);
    ASSERT_EQ(ctx_.memory.data[3], 1);
    ASSERT_EQ(ctx_.memory.data[4], 2);
    ASSERT_EQ(ctx_.memory.data[5], 0);
}

TEST_F(RuntimeTest, MStore8)
{
    ctx_.gas_remaining = 3;
    call(mstore8, 0, 0xFFFF);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.cost, 3);
    ASSERT_EQ(ctx_.memory.data[0], 0xFF);
    ASSERT_EQ(ctx_.memory.data[1], 0x00);

    call(mstore8, 1, 0xFF);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.cost, 3);
    ASSERT_EQ(ctx_.memory.data[0], 0xFF);
    ASSERT_EQ(ctx_.memory.data[1], 0xFF);

    ASSERT_EQ(
        call(mload, 0),
        0xFFFF000000000000000000000000000000000000000000000000000000000000_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.cost, 3);
}

TEST_F(RuntimeTest, MLoad)
{
    ctx_.gas_remaining = 6;
    call(mstore, 0, 0xFF);
    ASSERT_EQ(call(mload, 0), 0xFF);
    ASSERT_EQ(ctx_.gas_remaining, 3);
    ASSERT_EQ(ctx_.memory.cost, 3);

    ASSERT_EQ(call(mload, 1), 0xFF00);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.cost, 6);
}

TEST_F(RuntimeTest, QuadraticCosts)
{
    ctx_.gas_remaining = 101;
    ASSERT_EQ(call(mload, 1024), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.cost, 101);
    ASSERT_EQ(ctx_.memory.size, 1056);
}

TEST_F(RuntimeTest, ExpandMemory)
{
    ctx_.gas_remaining = 1'000'000;

    ASSERT_EQ(ctx_.memory.capacity, Memory::initial_capacity);

    uint32_t const new_capacity = (Memory::initial_capacity + 32) * 2;

    ctx_.expand_memory(Bin<30>::unsafe_from(Memory::initial_capacity + 1));
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity + 32);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 419);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    ctx_.expand_memory(Bin<30>::unsafe_from(Memory::initial_capacity + 90));
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity + 96);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 426);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    ctx_.expand_memory(Bin<30>::unsafe_from(new_capacity));
    ASSERT_EQ(ctx_.memory.size, new_capacity);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 904);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    ctx_.expand_memory(Bin<30>::unsafe_from(Memory::initial_capacity * 4 + 1));
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity * 4 + 32);
    ASSERT_EQ(ctx_.memory.capacity, (Memory::initial_capacity * 4 + 32) * 2);
    ASSERT_EQ(ctx_.memory.cost, 2053);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));
}

TEST_F(RuntimeTest, ExpandMemoryNotUsingCachedAllocatorFreeRegression)
{
    ASSERT_EQ(EvmMemoryAllocatorMeta::cache_list.size(), 0);

    ctx_.gas_remaining = 1'000'000;
    ctx_.expand_memory(Bin<30>::unsafe_from(Memory::initial_capacity + 1));

    ASSERT_EQ(EvmMemoryAllocatorMeta::cache_list.size(), 1);
}

TEST_F(RuntimeTest, RuntimeIncreaseMemory)
{
    ctx_.gas_remaining = 1'000'000;

    ASSERT_EQ(ctx_.memory.capacity, Memory::initial_capacity);

    uint32_t const new_capacity = (Memory::initial_capacity + 32) * 2;

    monad_vm_runtime_increase_memory(
        Bin<30>::unsafe_from(Memory::initial_capacity + 1), &ctx_);
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity + 32);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 419);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    monad_vm_runtime_increase_memory(
        Bin<30>::unsafe_from(Memory::initial_capacity + 90), &ctx_);
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity + 96);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 426);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    monad_vm_runtime_increase_memory(Bin<30>::unsafe_from(new_capacity), &ctx_);
    ASSERT_EQ(ctx_.memory.size, new_capacity);
    ASSERT_EQ(ctx_.memory.capacity, new_capacity);
    ASSERT_EQ(ctx_.memory.cost, 904);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));

    monad_vm_runtime_increase_memory(
        Bin<30>::unsafe_from(Memory::initial_capacity * 4 + 1), &ctx_);
    ASSERT_EQ(ctx_.memory.size, Memory::initial_capacity * 4 + 32);
    ASSERT_EQ(ctx_.memory.capacity, (Memory::initial_capacity * 4 + 32) * 2);
    ASSERT_EQ(ctx_.memory.cost, 2053);
    ASSERT_TRUE(std::all_of(
        ctx_.memory.data, ctx_.memory.data + ctx_.memory.size, [](auto b) {
            return b == 0;
        }));
}
