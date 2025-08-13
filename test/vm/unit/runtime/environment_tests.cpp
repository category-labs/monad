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

#include <category/vm/runtime/environment.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

TEST_F(RuntimeTest, SelfBalance)
{
    host_.accounts[0x0000000000000000000000000000000000000001_address]
        .set_balance(100);

    ASSERT_EQ(call(selfbalance), 100);
}

TEST_F(RuntimeTest, BlockHashOld)
{
    ASSERT_EQ(call(blockhash, 1000), 0);
    ASSERT_EQ(call(blockhash, 23527), 0);
}

TEST_F(RuntimeTest, BlockHashCurrent)
{
    constexpr auto hash =
        0x105DF6064F84551C4100A368056B8AF0E491077245DAB1536D2CFA6AB78421CE_u256;

    ASSERT_EQ(call(blockhash, 23528), hash);
    ASSERT_EQ(call(blockhash, 23660), hash);
    ASSERT_EQ(call(blockhash, 23783), hash);
}

TEST_F(RuntimeTest, BlockHashNew)
{
    ASSERT_EQ(call(blockhash, 23784), 0);
    ASSERT_EQ(call(blockhash, 30000), 0);
}

TEST_F(RuntimeTest, BlobHash)
{
    ASSERT_EQ(call(blobhash, 0), 1);
    ASSERT_EQ(call(blobhash, 1), 2);
    ASSERT_EQ(call(blobhash, 2), 0);
    ASSERT_EQ(call(blobhash, 3), 0);
}
