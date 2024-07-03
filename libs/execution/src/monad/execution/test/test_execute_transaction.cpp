#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/intrinsic_gas_buffer.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <optional>

using namespace monad;

using db_t = TrieDb;

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    using intx::operator"" _u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
    };

    BlockHeader const header{.number = 17034870, .beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    EthereumMainnet chain;
    auto const result = execute_impl<EVMC_SHANGHAI>(
        chain, 0, tx, from, header, block_hash_buffer, bs, prev);

    ASSERT_TRUE(!result.has_error());

    auto const &receipt = result.value();

    EXPECT_EQ(receipt.status, 1u);
    {
        State state{bs, Incarnation{0, 0}};
        EXPECT_EQ(
            intx::be::load<uint256_t>(state.get_balance(from)),
            uint256_t{55'999'999'999'470'000});
        EXPECT_EQ(state.get_nonce(from), 26); // EVMC will inc for creation
    }

    // check if miner gets the right reward
    EXPECT_EQ(receipt.gas_used * 10u, uint256_t{530'000});
}

TEST(ExecuteTransaction, exhaust_reserve_balance)
{
    using intx::operator"" _u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256,
             .chain_id = 41454},
        .nonce = 25,
        .max_fee_per_gas = 1,
        .gas_limit = 55'000,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    IntrinsicGasBuffer buf;
    MonadDevnet chain{buf};

    {
        buf.set_block_number(1);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
        auto const &receipt = result.value();
        EXPECT_EQ(receipt.gas_used, 53'000);
        EXPECT_EQ(receipt.status, 1);
    }

    {
        buf.set_block_number(2);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 26;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
    }

    {
        buf.set_block_number(3);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 27;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
    }

    {
        buf.set_block_number(4);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 28;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), TransactionError::InsufficientReserveBalance);
    }
}

TEST(ExecuteTransaction, exhaust_reserve_balance_less_than_default)
{
    using intx::operator"" _u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 150'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256,
             .chain_id = 41454},
        .nonce = 25,
        .max_fee_per_gas = 1,
        .gas_limit = 53'000,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    IntrinsicGasBuffer buf;
    MonadDevnet chain{buf};

    {
        buf.set_block_number(1);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
        auto const &receipt = result.value();
        EXPECT_EQ(receipt.gas_used, 53'000);
        EXPECT_EQ(receipt.status, 1);
    }

    {
        buf.set_block_number(2);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 26;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
    }

    {
        buf.set_block_number(3);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 27;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), TransactionError::InsufficientReserveBalance);
    }
}

TEST(ExecuteTransaction, insufficient_execution_balance)
{
    using intx::operator"" _u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256,
             .chain_id = 41454},
        .nonce = 25,
        .max_fee_per_gas = 1,
        .gas_limit = 55'000,
        .value = 56'000'000'000'000'000};

    BlockHeader const header{.beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    IntrinsicGasBuffer buf;
    MonadDevnet chain{buf};

    {
        buf.set_block_number(1);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
        auto const &receipt = result.value();
        EXPECT_EQ(receipt.gas_used, 53'000);
        EXPECT_EQ(receipt.status, 0);
        auto const acct = bs.read_account(from);
        ASSERT_TRUE(acct.has_value());
        EXPECT_EQ(acct->nonce, 26);
        EXPECT_EQ(acct->balance, 55'999'999'999'947'000);
    }
}

TEST(ExecuteTransaction, replenish_reserve_balance)
{
    using intx::operator"" _u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256,
             .chain_id = 41454},
        .nonce = 25,
        .max_fee_per_gas = 1,
        .gas_limit = 55'000,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    IntrinsicGasBuffer buf;
    MonadDevnet chain{buf};

    {
        buf.set_block_number(1);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
        auto const &receipt = result.value();
        EXPECT_EQ(receipt.gas_used, 53'000);
        EXPECT_EQ(receipt.status, 1);
    }

    {
        buf.set_block_number(2);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 26;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
    }

    {
        buf.set_block_number(3);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 27;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
    }

    {
        buf.set_block_number(4);
        buf.set_block_number(5);
        boost::fibers::promise<void> prev{};
        prev.set_value();
        tx.nonce = 28;
        auto const result = execute_impl<EVMC_SHANGHAI>(
            chain, 0, tx, from, header, block_hash_buffer, bs, prev);
        ASSERT_TRUE(result.has_value());
        auto const &receipt = result.value();
        EXPECT_EQ(receipt.gas_used, 53'000);
        EXPECT_EQ(receipt.status, 1);
    }
}
