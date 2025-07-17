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
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/vm.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;
using namespace intx::literals;

struct Storage : public ::testing::Test
{
    static constexpr auto ADDRESS{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 1, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.touch(ADDRESS);
    }
};

TEST_F(Storage, variable)
{
    StorageVariable<u256_be> var(state, ADDRESS, bytes32_t{6000});
    ASSERT_FALSE(var.load_checked().has_value());
    var.store(5_u256);
    ASSERT_TRUE(var.load_checked().has_value());
    EXPECT_EQ(var.load().native(), 5_u256);
    var.store(2000_u256);
    EXPECT_EQ(var.load().native(), 2000_u256);
    var.clear();
    EXPECT_FALSE(var.load_checked().has_value());
}

TEST_F(Storage, struct)
{
    struct S
    {
        u32_be x;
        u32_be y;
        u256_be z;
    };

    StorageVariable<S> var(state, ADDRESS, bytes32_t{6000});

    ASSERT_FALSE(var.load_checked().has_value());
    var.store(S{.x = 4, .y = 5, .z = 6_u256});
    ASSERT_TRUE(var.load_checked().has_value());
    S s = var.load();
    EXPECT_EQ(s.x, 4);
    EXPECT_EQ(s.y, 5);
    EXPECT_EQ(s.z, 6_u256);
    s.x = s.x.native() * 2;
    s.y = s.y.native() * 2;
    s.z = s.z.native() * 2;
    var.store(s);
    ASSERT_TRUE(var.load_checked().has_value());
    S s2 = var.load();
    EXPECT_EQ(s2.x.native(), 8);
    EXPECT_EQ(s2.y.native(), 10);
    EXPECT_EQ(s2.z.native(), 12);
    var.clear();
    EXPECT_FALSE(var.load_checked().has_value());
}

TEST_F(Storage, array)
{
    struct SomeType
    {
        u256_be blob;
        u32_be counter;
    };

    StorageArray<SomeType> arr(state, ADDRESS, bytes32_t{100});
    EXPECT_EQ(arr.length(), 0);

    for (uint32_t i = 0; i < 100; ++i) {
        arr.push(SomeType{.blob = 2000_u256, .counter = i});
        EXPECT_EQ(arr.length(), i + 1);
    }

    for (uint32_t i = 0; i < 100; ++i) {
        auto const res = arr.get(i);
        ASSERT_TRUE(res.load_checked().has_value())
            << "Could not load at index: " << i << std::endl;
        EXPECT_EQ(res.load().counter.native(), i);
    }

    for (uint32_t i = 100; i > 0; --i) {
        arr.pop();
        EXPECT_EQ(arr.length(), i - 1);
    }
}
