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
    EXPECT_EQ(get_v({.signature = {.y_parity = false}}), 27);
    EXPECT_EQ(get_v({.signature = {.y_parity = true}}), 28);
    // EIP-155
    EXPECT_EQ(get_v({.signature = {.y_parity = false}, .chain_id = 1}), 37);
    EXPECT_EQ(get_v({.signature = {.y_parity = true}, .chain_id = 1}), 38);
    EXPECT_EQ(get_v({.signature = {.y_parity = false}, .chain_id = 5}), 45);
    EXPECT_EQ(get_v({.signature = {.y_parity = true}, .chain_id = 5}), 46);
}

TEST(Signature, from_v)
{
    // Legacy - no chain id
    {
        SignatureAndChain sc{};
        sc.from_v(27);
        EXPECT_EQ(sc.signature.y_parity, false);
        sc.from_v(28);
        EXPECT_EQ(sc.signature.y_parity, true);
    }

    // EIP-155
    {
        SignatureAndChain sc{};
        sc.from_v(37);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.signature.y_parity, false);
        sc.from_v(38);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.signature.y_parity, true);
    }
    {
        SignatureAndChain sc{};
        sc.from_v(45);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.signature.y_parity, false);
        sc.from_v(46);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.signature.y_parity, true);
    }
}

TEST(Signature, is_valid_boundaries)
{
    constexpr auto n = Secp256k1Signature::secp256k1_order;
    constexpr auto half_n = Secp256k1Signature::secp256k1_order_half;

    // Sanity: minimal valid signature (r = 1, s = 1).
    EXPECT_TRUE((Secp256k1Signature{.r = 1, .s = 1}).is_valid());

    // r = 0 or s = 0 is rejected.
    EXPECT_FALSE((Secp256k1Signature{.r = 0, .s = 1}).is_valid());
    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = 0}).is_valid());
    EXPECT_FALSE((Secp256k1Signature{.r = 0, .s = 0}).is_valid());

    // r or s == n is rejected (must be strictly less than the group order).
    EXPECT_FALSE((Secp256k1Signature{.r = n, .s = 1}).is_valid());
    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = n}).is_valid());

    // r or s == n - 1 is rejected via the low-s rule for s, but r = n - 1 is
    // accepted (only s is constrained by EIP-2).
    EXPECT_TRUE((Secp256k1Signature{.r = n - 1, .s = 1}).is_valid());
    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = n - 1}).is_valid());

    // EIP-2 low-s boundary: s == n/2 is valid, s == n/2 + 1 is not.
    EXPECT_TRUE((Secp256k1Signature{.r = 1, .s = half_n}).is_valid());
    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = half_n + 1}).is_valid());
}

TEST(Signature, has_upper_s_boundary)
{
    constexpr auto half_n = Secp256k1Signature::secp256k1_order_half;

    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = 1}).has_upper_s());
    EXPECT_FALSE((Secp256k1Signature{.r = 1, .s = half_n}).has_upper_s());
    EXPECT_TRUE((Secp256k1Signature{.r = 1, .s = half_n + 1}).has_upper_s());
}
