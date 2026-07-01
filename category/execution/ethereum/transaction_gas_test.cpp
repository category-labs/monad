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
    template <monad_eth_revision r>
    using rev = std::integral_constant<monad_eth_revision, r>;

    constexpr auto sender = 0x000000000000000000000000000000000000000a_address;
    constexpr auto recipient =
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
}

// Intrinsic gas across every revision. Each assertion branches on
// EIP-2780 (eip_2780_active(), i.e. Amsterdam+): the flat 21000/32000 model for
// pre-Amsterdam, the decomposed base + recipient/value charges for Amsterdam.
//
// monad charges the transfer-log cost (TRANSFER_LOG_COST = 1756) at the point
// of logging (EIP-7708's emit_native_transfer_event), gated on the log EIP,
// rather than bundling it into intrinsic as the EIP-2780 table does. So
// intrinsic_gas here EXCLUDES it: value-to-other is 19244 (EIP table 21000) and
// create-with-value is 23000 (EIP table 24756); the missing 1756 is charged
// when the Transfer log is emitted, so the total still matches the fixtures.
//
// Also out of scope here: the delegation rows (18000/24000) — the
// delegation-target COLD_ACCOUNT_ACCESS is charged at top-frame call
// resolution — and the new-account 183600 (EIP-8037 state gas).
TYPED_TEST(TraitsTest, intrinsic_gas)
{
    using Trait = typename TestFixture::Trait;
    static_assert(Trait::evm_rev() >= MONAD_ETH_ISTANBUL);

    // Components unchanged by EIP-2780, gated on their introducing fork.
    constexpr uint64_t zero_token = 4; // EIP-2028
    constexpr uint64_t non_zero_token = 16; // EIP-2028
    constexpr uint64_t init_word = // EIP-3860, creation only
        Trait::evm_rev() >= MONAD_ETH_SHANGHAI ? 2u : 0u;
    constexpr uint64_t al_addr = // EIP-2930
        Trait::evm_rev() >= MONAD_ETH_BERLIN ? 2'400u : 0u;
    constexpr uint64_t al_key =
        Trait::evm_rev() >= MONAD_ETH_BERLIN ? 1'900u : 0u;

    // EIP-2780 decomposes the flat base into explicit per-case charges.
    constexpr bool eip_2780 = Trait::eip_2780_active();
    constexpr uint64_t create_base =
        eip_2780 ? (12'000u + 11'000u) : (21'000u + 32'000u);
    constexpr uint64_t call_base = eip_2780 ? 12'000u : 21'000u;
    constexpr uint64_t cold = eip_2780 ? 3'000u : 0u; // recipient cold access
    // TX_VALUE_COST only; the transfer-log cost is charged at log emission
    // (EIP-7708), not in intrinsic.
    constexpr uint64_t value_xfer = eip_2780 ? 4'244u : 0u;

    auto const ig = [](Transaction const &t) {
        return intrinsic_gas<Trait>(t, sender);
    };

    // Self-transfer, value > 0 (EIP-2780 waives recipient + value charges).
    {
        Transaction t{.value = 1};
        t.to = sender;
        EXPECT_EQ(ig(t), call_base);
    }

    // Zero-value transaction to any address
    {
        Transaction t{};
        t.to = recipient;
        EXPECT_EQ(ig(t), call_base + cold);
    }

    // Value transfer
    // TODO: EIP-7708 should add transfer log cost of 1756
    {
        Transaction t{.value = 1};
        t.to = recipient;
        EXPECT_EQ(ig(t), call_base + cold + value_xfer);
    }

    // Contract creation, value 0.
    {
        Transaction const t{};
        EXPECT_EQ(ig(t), create_base);
    }

    // Contract creation, value > 0.
    // TODO: EIP-7708 should add transfer log cost of 1756
    {
        Transaction const t{.value = 1};
        EXPECT_EQ(ig(t), create_base);
    }

    // Creation calldata token cost + per-word initcode cost.
    // TODO: EIP-7708 should add transfer log cost of 1756
    {
        Transaction t{};
        t.data.push_back(0x00);
        EXPECT_EQ(ig(t), create_base + zero_token + init_word);

        t.data.push_back(0xff);
        EXPECT_EQ(ig(t), create_base + zero_token + non_zero_token + init_word);
    }

    // Creation with larger calldata (128 bytes => 4 init words).
    // TODO: EIP-7708 should add transfer log cost of 1756
    {
        byte_string data;
        for (auto i = 0; i < 127; ++i) {
            data.push_back(0xc0);
        }
        data.push_back(0x00);

        Transaction const t{.data = data};
        EXPECT_EQ(
            ig(t),
            create_base + non_zero_token * 127 + zero_token + 4 * init_word);
    }

    // Call calldata token cost (no initcode cost when `to` is set).
    {
        Transaction t{};
        t.to = recipient;
        t.data.push_back(0x00);
        EXPECT_EQ(ig(t), call_base + cold + zero_token);

        t.data.push_back(0xff);
        EXPECT_EQ(ig(t), call_base + cold + zero_token + non_zero_token);
    }

    // Access list (EIP-2930). The recipient cold-access charge is still applied
    // on top: access lists do not warm tx-level accounts under EIP-2780.
    {
        Transaction t{};
        t.to = recipient;

        static constexpr auto key1{
            0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
        static constexpr auto key2{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
        t.access_list.push_back({*t.to, {key1, key2}});
        EXPECT_EQ(ig(t), call_base + cold + al_addr + 2 * al_key);

        t.data.push_back(0x00);
        t.data.push_back(0xff);
        EXPECT_EQ(
            ig(t),
            call_base + cold + al_addr + 2 * al_key + zero_token +
                non_zero_token);
    }
}

// EIP-7623 calldata floor. Its base follows the EIP-2780 reduced base.
TYPED_TEST(TraitsTest, floor_data_gas)
{
    using Trait = typename TestFixture::Trait;

    constexpr uint64_t base = Trait::eip_2780_active() ? 12'000u : 21'000u;

    {
        Transaction t{};
        t.to = recipient; // no calldata
        EXPECT_EQ(floor_data_gas<Trait>(t), base);
    }

    {
        Transaction t{};
        t.to = recipient;
        t.data.push_back(0x00); // 1 zero token
        t.data.push_back(0xff); // 1 non-zero token
        EXPECT_EQ(floor_data_gas<Trait>(t), base + 10 + 40);
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
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_LONDON) {
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

TYPED_TEST(TraitsTest, blob_schedule)
{
    if constexpr (TestFixture::Trait::eip_7691_active()) {
        EXPECT_EQ(max_blobs_per_block<typename TestFixture::Trait>(), 9);
        EXPECT_EQ(
            blob_base_fee_update_fraction<typename TestFixture::Trait>(),
            5'007'716);
    }
    else {
        EXPECT_EQ(max_blobs_per_block<typename TestFixture::Trait>(), 6);
        EXPECT_EQ(
            blob_base_fee_update_fraction<typename TestFixture::Trait>(),
            3'338'477);
    }
}
