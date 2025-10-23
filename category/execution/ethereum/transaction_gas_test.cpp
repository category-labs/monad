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

#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/traits.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

namespace
{
    template <evmc_revision r>
    using rev = std::integral_constant<evmc_revision, r>;
}

TYPED_TEST(TraitsTest, intrinsic_gas)
{
    auto non_zero_since = []<evmc_revision r>(rev<r>, uint64_t val) consteval {
        if constexpr (TestFixture::Trait::evm_rev() >= r) {
            return val;
        }
        else {
            return 0;
        }
    };

    static constexpr auto empty_to =
        non_zero_since(rev<EVMC_HOMESTEAD>{}, 32'000);

    {
        Transaction t{};
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t), 21'000 + empty_to);
    }

    {
        Transaction t{};
        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<typename TestFixture::Trait>(t), 21'000);
    }

    static constexpr auto zero_token_cost = 4;
    static constexpr auto non_zero_token_cost = [] {
        if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
            // EIP-2028
            return 68;
        }
        else {
            return 16;
        }
    }();

    // EIP-3860
    // only charged when tx.to is not set
    static constexpr auto extra_cost_per_evm_word =
        non_zero_since(rev<EVMC_SHANGHAI>{}, 2);

    {
        Transaction t{};

        t.data.push_back(0x00);
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + empty_to + zero_token_cost + extra_cost_per_evm_word);

        t.data.push_back(0xff);
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + empty_to + zero_token_cost + non_zero_token_cost +
                extra_cost_per_evm_word);
    }

    {
        byte_string data;
        for (auto i = 0; i < 127; ++i) {
            data.push_back(0xc0);
        }
        data.push_back(0x00);

        Transaction const t{.data = data};

        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + empty_to + non_zero_token_cost * 127 + zero_token_cost +
                4 * extra_cost_per_evm_word);
    }

    {
        Transaction t{};
        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;

        t.data.push_back(0x00);
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + zero_token_cost);

        t.data.push_back(0xff);
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + zero_token_cost + non_zero_token_cost);
    }

    // EIP-2930
    static constexpr auto cost_per_access_list_address =
        non_zero_since(rev<EVMC_BERLIN>{}, 2'400);
    static constexpr auto cost_per_access_list_key =
        non_zero_since(rev<EVMC_BERLIN>{}, 1'900);

    {
        Transaction t{};
        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;

        static constexpr auto key1{
            0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
        static constexpr auto key2{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
        t.access_list.push_back({*t.to, {key1, key2}});
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + cost_per_access_list_address +
                2 * cost_per_access_list_key);

        t.data.push_back(0x00);
        t.data.push_back(0xff);
        EXPECT_EQ(
            intrinsic_gas<typename TestFixture::Trait>(t),
            21'000 + cost_per_access_list_address +
                2 * cost_per_access_list_key + zero_token_cost +
                non_zero_token_cost);
    }
}

TYPED_TEST(TraitsTest, txn_award)
{
    // gas price
    Transaction const t0{.max_fee_per_gas = 1'000};
    Transaction const t1{
        .max_fee_per_gas = 3'000,
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 1'000};
    Transaction const t2{
        .max_fee_per_gas = 3'000, .type = TransactionType::legacy};
    Transaction const t3{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 1'000};
    Transaction const t4{
        .max_fee_per_gas = 5'000, .type = TransactionType::eip1559};
    Transaction const t5{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 4'000};

    EXPECT_EQ(gas_price<typename TestFixture::Trait>(t0, 0u), 1'000);
    EXPECT_EQ(gas_price<typename TestFixture::Trait>(t1, 2'000u), 3'000);
    EXPECT_EQ(gas_price<typename TestFixture::Trait>(t2, 2'000u), 3'000);
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_LONDON) {
        EXPECT_EQ(gas_price<typename TestFixture::Trait>(t3, 2'000u), 5'000);
        EXPECT_EQ(gas_price<typename TestFixture::Trait>(t4, 2'000u), 5'000);
    }
    else {
        EXPECT_EQ(gas_price<typename TestFixture::Trait>(t3, 2'000u), 3'000);
        EXPECT_EQ(gas_price<typename TestFixture::Trait>(t4, 2'000u), 2'000);
    }
    EXPECT_EQ(gas_price<typename TestFixture::Trait>(t5, 2'000u), 5'000);

    // txn award
    EXPECT_EQ(
        calculate_txn_award<typename TestFixture::Trait>(
            Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
        uint256_t{9'000'000'000'000'000'000});
}
