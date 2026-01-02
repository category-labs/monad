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

#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/block_db.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

using namespace monad;

TEST(Transaction, recover_sender_block_2730000)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(2'730'000u, block);
    ASSERT_TRUE(res);

    EXPECT_EQ(block.transactions.size(), 4u);

    auto const sender0 = recover_sender(block.transactions[0]);
    EXPECT_EQ(
        sender0.value(), 0x2a65Aca4D5fC5B5C859090a6c34d164135398226_address);

    auto const sender1 = recover_sender(block.transactions[1]);
    EXPECT_EQ(
        sender1.value(), 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);

    auto const sender2 = recover_sender(block.transactions[2]);
    EXPECT_EQ(
        sender2.value(), 0x2a65Aca4D5fC5B5C859090a6c34d164135398226_address);

    auto const sender3 = recover_sender(block.transactions[3]);
    EXPECT_EQ(
        sender3.value(), 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);
}

TEST(TransactionProcessor, recover_sender_block_14000000)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(14'000'000u, block);
    ASSERT_TRUE(res);

    EXPECT_EQ(block.transactions.size(), 112u);
    EXPECT_EQ(
        *block.transactions[0].to,
        0x9008D19f58AAbD9eD0D60971565AA8510560ab41_address);

    auto const sender0 = recover_sender(block.transactions[0]);
    EXPECT_EQ(
        sender0.value(), 0xdE1c59Bc25D806aD9DdCbe246c4B5e5505645718_address);

    auto const sender1 = recover_sender(block.transactions[1]);
    EXPECT_EQ(
        sender1.value(), 0xf60c2Ea62EDBfE808163751DD0d8693DCb30019c_address);

    auto const sender2 = recover_sender(block.transactions[2]);
    EXPECT_EQ(
        sender2.value(), 0x26d396446BD1EEf51EA972487BDf7A83197c27bF_address);

    auto const sender3 = recover_sender(block.transactions[3]);
    EXPECT_EQ(
        sender3.value(), 0x8Ce36461B8aC28B0eaF1d2466e05ED4fa4DE3B9e_address);
}

TEST(TransactionProcessor, no_recover_high_s_auth)
{
    using namespace intx::literals;

    constexpr auto malleate = [](AuthorizationEntry const &auth) {
        constexpr auto secp256k1_n =
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141_u256;

        return AuthorizationEntry{
            .sc =
                {
                    .r = auth.sc.r,
                    .s = secp256k1_n - auth.sc.s,
                    .chain_id = auth.sc.chain_id,
                    .y_parity = auth.sc.y_parity == 1 ? uint8_t{0} : uint8_t{1},
                },
            .address = auth.address,
            .nonce = auth.nonce,
        };
    };

    constexpr auto original_auth_tuple = AuthorizationEntry{
        .sc =
            {
                .r =
                    20024342273895419273789557730553770517558589916489577758020700015851504969560_u256,
                .s =
                    53058432675938613889995545562274668230314193454921684363060655866328293077815_u256,
                .chain_id = 20143,
                .y_parity = 0,
            },
        .address = 0xdeadbeef00000000000000000000000000000000_address,
        .nonce = 0,
    };

    static_assert(!original_auth_tuple.sc.has_upper_s());

    auto const original_authority = recover_authority(original_auth_tuple);
    EXPECT_TRUE(original_authority.has_value());
    EXPECT_EQ(
        original_authority.value(),
        0xC7f24cEF4eeD1F110196d7D939b388ac1CaEb21d_address);

    constexpr auto malleated_auth_tuple = malleate(original_auth_tuple);
    static_assert(malleated_auth_tuple.sc.has_upper_s());

    // We could recover the authority from the low-s one, but not from its
    // correctly malleated high-s version
    auto const malleated_authority = recover_authority(malleated_auth_tuple);
    EXPECT_FALSE(malleated_authority.has_value());
}
