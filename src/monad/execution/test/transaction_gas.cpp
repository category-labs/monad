#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(TransactionGas, intrinsic_gas)
{
    // Frontier
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'000);

        t.data.push_back(0x00);
        EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'004);

        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'072);
    }

    // Homestead
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::homestead>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<fork_traits::homestead>(t), 21'000);
    }

    // Spurious Dragon
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::spurious_dragon>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<fork_traits::spurious_dragon>(t), 21'000);
    }

    // Byzantium
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::byzantium>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<fork_traits::byzantium>(t), 21'000);
    }

    // Istanbul
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        t.data.push_back(0x00);
        EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 21'004);

        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 21'020);
    }

    // Berlin
    {
        Transaction t{};
        EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 53'000);

        t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
        EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 21'000);

        static constexpr auto key1{
            0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
        static constexpr auto key2{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
        t.access_list.push_back({*t.to, {key1, key2}});
        EXPECT_EQ(
            intrinsic_gas<fork_traits::berlin>(t), 21'000 + 2400 + 1900 + 1900);

        t.data.push_back(0x00);
        t.data.push_back(0xff);
        EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 27'220);
    }

    // Shanghai EIP-3860
    {
        byte_string data;
        for (auto i = 0u; i < uint64_t{0x80}; ++i) {
            data += {0xc0};
        }

        Transaction t{.data = data};

        EXPECT_EQ(
            intrinsic_gas<fork_traits::shanghai>(t),
            32'000u + 21'000u + 16u * 128u + 0u + 4u * 2u);
    }
}

TEST(TransactionGas, txn_award)
{
    // Frontier
    {
        // gas price
        EXPECT_EQ(
            gas_price<fork_traits::frontier>(
                Transaction{.max_fee_per_gas = 1'000}, 0u),
            1'000);

        // txn award
        EXPECT_EQ(
            calculate_txn_award<fork_traits::frontier>(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }

    // London
    {
        // gas price
        Transaction t1{
            .max_fee_per_gas = 3'000,
            .type = TransactionType::eip155,
            .max_priority_fee_per_gas = 1'000};
        Transaction t2{
            .max_fee_per_gas = 3'000, .type = TransactionType::eip155};
        Transaction t3{
            .max_fee_per_gas = 5'000,
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 1'000};
        Transaction t4{
            .max_fee_per_gas = 5'000, .type = TransactionType::eip1559};
        Transaction t5{
            .max_fee_per_gas = 5'000,
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 4'000};
        EXPECT_EQ(gas_price<fork_traits::london>(t1, 2'000u), 3'000);
        EXPECT_EQ(gas_price<fork_traits::london>(t2, 2'000u), 3'000);
        EXPECT_EQ(gas_price<fork_traits::london>(t3, 2'000u), 3'000);
        EXPECT_EQ(gas_price<fork_traits::london>(t4, 2'000u), 2'000);
        EXPECT_EQ(gas_price<fork_traits::london>(t5, 2'000u), 5'000);

        // txn award
        EXPECT_EQ(
            calculate_txn_award<fork_traits::london>(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }
}
