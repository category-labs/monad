// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#include <category/execution/monad/private_domain_fee.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(PrivateDomainFee, price_is_50_gwei)
{
    EXPECT_EQ(DOMAIN_GAS_PRICE, uint256_t{50} * 1'000'000'000);
}

TEST(PrivateDomainFee, fee_buys_gas_rounding_down)
{
    constexpr uint64_t BLOCK_GAS_LIMIT = 150'000'000;
    EXPECT_EQ(purchased_domain_gas(0, BLOCK_GAS_LIMIT), 0);
    EXPECT_EQ(purchased_domain_gas(DOMAIN_GAS_PRICE - 1, BLOCK_GAS_LIMIT), 0);
    EXPECT_EQ(purchased_domain_gas(DOMAIN_GAS_PRICE, BLOCK_GAS_LIMIT), 1);
    EXPECT_EQ(
        purchased_domain_gas(DOMAIN_GAS_PRICE * 21'000 + 7, BLOCK_GAS_LIMIT),
        21'000);
}

TEST(PrivateDomainFee, gas_is_capped_at_the_block_gas_limit)
{
    constexpr uint64_t BLOCK_GAS_LIMIT = 150'000'000;
    EXPECT_EQ(
        purchased_domain_gas(
            DOMAIN_GAS_PRICE * BLOCK_GAS_LIMIT, BLOCK_GAS_LIMIT),
        BLOCK_GAS_LIMIT);
    EXPECT_EQ(
        purchased_domain_gas(
            DOMAIN_GAS_PRICE * (BLOCK_GAS_LIMIT + 1), BLOCK_GAS_LIMIT),
        BLOCK_GAS_LIMIT);
    EXPECT_EQ(
        purchased_domain_gas(uint256_t{1} << 200, BLOCK_GAS_LIMIT),
        BLOCK_GAS_LIMIT);
}
