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
    bool const res =
        block_db.get(CHAIN_CONFIG_ETHEREUM_MAINNET, 2'730'000u, block);
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
    bool const res =
        block_db.get(CHAIN_CONFIG_ETHEREUM_MAINNET, 14'000'000u, block);
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
