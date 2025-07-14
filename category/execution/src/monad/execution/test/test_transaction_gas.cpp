#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

TEST(TransactionGas, intrinsic_gas)
{
    // Frontier
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_FRONTIER>(t), 21'000);

        t.data.push_back(0x00);
        EXPECT_EQ(intrinsic_gas<EVMC_FRONTIER>(t), 21'004);

        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<EVMC_FRONTIER>(t), 21'072);
    }

    // Homestead
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_HOMESTEAD>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<EVMC_HOMESTEAD>(t), 21'000);
    }

    // Spurious Dragon
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_SPURIOUS_DRAGON>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<EVMC_SPURIOUS_DRAGON>(t), 21'000);
    }

    // Byzantium
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_BYZANTIUM>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<EVMC_BYZANTIUM>(t), 21'000);
    }

    // Istanbul
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_ISTANBUL>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        t.data.push_back(0x00);
        EXPECT_EQ(intrinsic_gas<EVMC_ISTANBUL>(t), 21'004);

        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<EVMC_ISTANBUL>(t), 21'020);
    }

    // Berlin
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<EVMC_BERLIN>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<EVMC_BERLIN>(t), 21'000);

        static constexpr auto key1{
            0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
        static constexpr auto key2{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
        t.access_list.push_back({*t.to, {key1, key2}});
        EXPECT_EQ(intrinsic_gas<EVMC_BERLIN>(t), 21'000 + 2400 + 1900 + 1900);

        t.data.push_back(0x00);
        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<EVMC_BERLIN>(t), 27'220);
    }

    // Shanghai EIP-3860
    {
        byte_string data;
        for (auto i = 0u; i < uint64_t{0x80}; ++i) {
            data += {0xc0};
        }

        Transaction const t{.data = data};

        EXPECT_EQ(
            intrinsic_gas<EVMC_SHANGHAI>(t),
            32'000u + 21'000u + 16u * 128u + 0u + 4u * 2u);
    }
}

TEST(TransactionGas, txn_award)
{
    // Frontier
    {
        // gas price
        EXPECT_EQ(
            gas_price<EVMC_FRONTIER>(Transaction{.max_fee_per_gas = 1'000}, 0u),
            1'000);

        // txn award
        EXPECT_EQ(
            calculate_txn_award<EVMC_FRONTIER>(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }

    // London
    {
        // gas price
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
        EXPECT_EQ(gas_price<EVMC_LONDON>(t1, 2'000u), 3'000);
        EXPECT_EQ(gas_price<EVMC_LONDON>(t2, 2'000u), 3'000);
        EXPECT_EQ(gas_price<EVMC_LONDON>(t3, 2'000u), 3'000);
        EXPECT_EQ(gas_price<EVMC_LONDON>(t4, 2'000u), 2'000);
        EXPECT_EQ(gas_price<EVMC_LONDON>(t5, 2'000u), 5'000);

        // txn award
        EXPECT_EQ(
            calculate_txn_award<EVMC_LONDON>(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }
}
