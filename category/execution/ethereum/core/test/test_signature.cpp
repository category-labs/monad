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

#include <category/execution/ethereum/core/signature.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(Signature, get_v)
{
    // Legacy - no chain id
    EXPECT_EQ(get_v({.y_parity = false}), 27);
    EXPECT_EQ(get_v({.y_parity = true}), 28);
    // EIP-155
    EXPECT_EQ(get_v({.chain_id = 1, .y_parity = false}), 37);
    EXPECT_EQ(get_v({.chain_id = 1, .y_parity = true}), 38);
    EXPECT_EQ(get_v({.chain_id = 5, .y_parity = false}), 45);
    EXPECT_EQ(get_v({.chain_id = 5, .y_parity = true}), 46);
}

TEST(Signature, from_v)
{
    // Legacy - no chain id
    {
        SignatureAndChain sc{};
        sc.from_v(27);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(28);
        EXPECT_EQ(sc.y_parity, true);
    }

    // EIP-155
    {
        SignatureAndChain sc{};
        sc.from_v(37);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(38);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.y_parity, true);
    }
    {
        SignatureAndChain sc{};
        sc.from_v(45);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(46);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.y_parity, true);
    }
}
