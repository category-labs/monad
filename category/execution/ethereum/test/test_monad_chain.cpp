#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/execution/monad/fee_buffer.hpp>
#include <category/mpt/db.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(MonadChain, compute_gas_refund)
{
    MonadTestnet monad_chain;
    Transaction tx{.gas_limit = 21'000};

    BlockHeader before_fork{.number = 0, .timestamp = 0};
    BlockHeader after_fork{.number = 1, .timestamp = 1739559600};

    auto const refund_before_fork = monad_chain.compute_gas_refund(
        before_fork.number, before_fork.timestamp, tx, 20'000, 1000);
    auto const refund_after_fork = monad_chain.compute_gas_refund(
        after_fork.number, after_fork.timestamp, tx, 20'000, 1000);
    EXPECT_EQ(20'200, refund_before_fork - refund_after_fork);
}

TEST(MonadChain, get_max_code_size)
{
    MonadTestnet const chain;
    EXPECT_EQ(chain.get_max_code_size(0, 1739559600), MAX_CODE_SIZE_EIP170);
    EXPECT_EQ(chain.get_max_code_size(0, 1741978800), 128 * 1024);
}

TEST(MonadChain, Genesis)
{
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x1436534e54a22183ea29a2273b341cb50018ed066441ffd111cd263297caba35_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_FRONTIER>(header).has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }

    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadDevnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0xb711505d8f46fc921ae824f847f26c5c3657bf6c8b9dcf07ffdf3357a143bca9_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_FRONTIER>(header).has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadMainnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x0c47353304f22b1c15706367d739b850cda80b5c87bbc335014fef3d88deaac9_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet2 const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0xFE557D7B2B42D6352B985949AA37EDA10FB02C90FEE62EB29E68839F2FB72B31_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
}

TEST(MonadChain, validate_transaction)
{
    constexpr Address SENDER{1};
    // TODO: other chains
    {
        MonadDevnet const chain;
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        vm::VM vm;
        BlockState bs{tdb, vm};
        State state{bs, Incarnation{0, 0}};
        FeeBuffer fee_buffer;
        MonadChainContext context{.fee_buffer = fee_buffer};

        // 1. Valid errors still propagate
        state.set_nonce(SENDER, 10);
        auto res = chain.validate_transaction(
            0, 0, 0, Transaction{}, SENDER, state, &context);
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), TransactionError::BadNonce);

        // 2. InsufficentReserveBalance
        auto const max_reserve =
            get_max_reserve(chain.get_monad_revision(0, 0), SENDER);
        Transaction const tx1{
            .nonce = 10,
            .max_fee_per_gas = 1500000000000,
            .gas_limit = 1000000,
        };
        fee_buffer.set(0, bytes32_t{0}, bytes32_t{0});
        fee_buffer.note(
            0, SENDER, max_gas_cost(tx1.gas_limit, tx1.max_fee_per_gas));
        fee_buffer.propose();
        res = chain.validate_transaction(0, 0, 0, tx1, SENDER, state, &context);
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), TransactionError::InsufficientReserveBalance);

        // clear out
        fee_buffer.set(1, bytes32_t{1}, bytes32_t{0});
        fee_buffer.propose();
        fee_buffer.set(2, bytes32_t{2}, bytes32_t{1});
        fee_buffer.propose();
        fee_buffer.set(3, bytes32_t{3}, bytes32_t{2});
        fee_buffer.propose();

        // try it again
        state.add_to_balance(
            SENDER,
            max_reserve /
                100); // Add very small balance to ensure insufficient reserve
        Transaction const tx2{
            .nonce = 10, .max_fee_per_gas = 25000000000000, .gas_limit = 30000};
        fee_buffer.set(4, bytes32_t{4}, bytes32_t{3});
        fee_buffer.note(
            0, SENDER, max_gas_cost(tx2.gas_limit, tx2.max_fee_per_gas));
        fee_buffer.propose();
        res = chain.validate_transaction(0, 0, 0, tx2, SENDER, state, &context);
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), TransactionError::InsufficientReserveBalance);

        // 3. Success
        state.add_to_balance(
            SENDER, max_reserve); // Add full reserve amount instead of half
        res = chain.validate_transaction(0, 0, 0, tx2, SENDER, state, &context);
        ASSERT_TRUE(res.has_value());
    }
}

TEST(MonadChain, revert_transaction)
{
    constexpr Address SENDER{1};
    // TODO: other chains
    {
        MonadDevnet const chain;
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        vm::VM vm;
        BlockState bs{tdb, vm};
        FeeBuffer fee_buffer;
        MonadChainContext context{.fee_buffer = fee_buffer};

        {
            State state{bs, Incarnation{0, 0}};
            state.add_to_balance(SENDER, 100);
            ASSERT_TRUE(bs.can_merge(state));
            bs.merge(state);
        }

        // Test case 1: Small balance - should revert when spending
        {
            State state{bs, Incarnation{1, 0}};
            state.subtract_from_balance(SENDER, 50);

            // Set up fee buffer properly - need to note a transaction for index
            // 0
            fee_buffer.set(1, bytes32_t{1}, bytes32_t{0});
            fee_buffer.note(
                0,
                SENDER,
                50); // Fee of 50 wei (less than original balance 100)
            fee_buffer.propose();

            // Should revert because:
            // - Original balance: 100 wei (way below 1 MON reserve)
            // - Current balance: 50 wei (after spending 50)
            // - Protected balance: min(1e18 - 50, 100) = 100
            // - Since 50 < 100, transaction should be reverted
            EXPECT_TRUE(
                chain.revert_transaction(1, 0, 0, SENDER, state, &context));
        }

        // Test case 2: Large balance - should not revert
        constexpr Address SENDER2{2};
        {
            State state{bs, Incarnation{2, 0}};
            // Give SENDER2 more than 1 MON (reserve amount)
            uint256_t large_balance =
                uint256_t{2} * 1000000000000000000ULL; // 2 MON
            state.add_to_balance(SENDER2, large_balance);
            ASSERT_TRUE(bs.can_merge(state));
            bs.merge(state);
        }

        { // txn no reversion - sufficient balance
            State state{bs, Incarnation{3, 0}};
            // Spend a small amount, still well above reserve
            state.subtract_from_balance(
                SENDER2, 1000000000000000000ULL / 2); // 0.5 MON

            fee_buffer.set(3, bytes32_t{3}, bytes32_t{2});
            fee_buffer.note(
                0,
                SENDER2,
                1000000000000000000ULL); // 1 MON fee (less than 2 MON original)
            fee_buffer.propose();

            // Should not revert because:
            // - Original balance: 2 MON
            // - Current balance: 1.5 MON (after spending 0.5 MON)
            // - Protected balance: min(1 MON - 1 MON, 2 MON) = 0 MON
            // - Since 1.5 MON > 0 MON, transaction should not be reverted
            EXPECT_FALSE(
                chain.revert_transaction(3, 0, 0, SENDER2, state, &context));
        }

        // Test case 3: Large balance but spending into reserve - should revert
        constexpr Address SENDER3{3};
        {
            State state{bs, Incarnation{4, 0}};
            // Give SENDER3 a large balance (2 MON)
            uint256_t large_balance =
                uint256_t{2} * 1000000000000000000ULL; // 2 MON
            state.add_to_balance(SENDER3, large_balance);
            ASSERT_TRUE(bs.can_merge(state));
            bs.merge(state);
        }

        { // txn should revert - spending too much into reserve
            State state{bs, Incarnation{5, 0}};
            // Spend a large amount that goes into the reserve balance
            state.subtract_from_balance(
                SENDER3,
                1800000000000000000ULL); // 1.8 MON (leaving only 0.2 MON)

            fee_buffer.set(5, bytes32_t{5}, bytes32_t{4});
            fee_buffer.note(
                0, SENDER3, 500000000000000000ULL); // 0.5 MON fee (less than 2
                                                    // MON original)
            fee_buffer.propose();

            // Should revert because:
            // - Original balance: 2 MON
            // - Current balance: 0.2 MON (after spending 1.8 MON)
            // - Protected balance: min(1 MON - 0.5 MON, 2 MON) = 0.5 MON
            // - Since 0.2 MON < 0.5 MON, transaction should be reverted
            EXPECT_TRUE(
                chain.revert_transaction(5, 0, 0, SENDER3, state, &context));
        }
    }
}
