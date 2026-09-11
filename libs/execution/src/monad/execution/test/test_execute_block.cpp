#include <monad/chain/monad_testnet.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>
#include <boost/fiber/future/promise.hpp>

#include <memory>
#include <optional>
#include <vector>

#include <gtest/gtest.h>

using namespace monad;
using db_t = TrieDb;
using intx::operator"" _u256;

// EVM version under test (used in all default test cases)
static constexpr auto rev = EVMC_SHANGHAI; 

TEST(ExecuteBlock, empty_block_execution_succeeds)
{
    // Setup test inputs
    static constexpr auto bene{0x5353535353535353535353535353535353535353_address};

    // Setup objects needed (default state)
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState block_state{tdb};
    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer{};
    fiber::PriorityPool priority_pool{2, 2};

    // Allocate state for the block
    std::vector<Transaction> transactions = {};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};

    // Create the current Block of TXs / other state
    auto block = Block{
        .header = header,
        .transactions = std::move(transactions),
        .ommers = std::move(ommers),
        .withdrawals = std::move(withdrawals),
    };

    // Execute the block and modify the block state!
    auto const results = execute_block(
        MonadTestnet{}, rev, block, block_state, block_hash_buffer, priority_pool);

    // Check execution results
    ASSERT_TRUE(!results.has_error());
    ASSERT_EQ(results.value().size(), 0);
}

TEST(ExecuteBlock, single_tx_block_execution_succeeds)
{
    // Setup test inputs
    static constexpr auto bene{0x5353535353535353535353535353535353535353_address};
    static constexpr auto sender{0x192cb97900c522fe1c7062c0620ebca8e6f55320_address};

    // Setup objects needed (default state)
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState block_state{tdb};
    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer{};
    fiber::PriorityPool priority_pool{2, 2};

    // Setup state beforehand (inject balances, nonces etc.)
    {
        State state{block_state, Incarnation{0, 0}};
        state.add_to_balance(sender, 100'000'000);
        state.set_nonce(sender, 25);
        block_state.merge(state);
    }

    // Create a TX
    Transaction const tx{
        .sc = {
            .r = 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
            .s = 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256
        },
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
    };

    // Allocate state for the block
    std::vector<Transaction> transactions = {tx};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};

    // Create the current Block of TXs / other state
    auto block = Block{
        .header = header,
        .transactions = std::move(transactions),
        .ommers = std::move(ommers),
        .withdrawals = std::move(withdrawals),
    };

    // Execute the block and modify the block state!
    auto const results = execute_block(
        MonadTestnet{}, rev, block, block_state, block_hash_buffer, priority_pool);

    // Check execution results
    ASSERT_TRUE(!results.has_error());
    for (auto const& exec_result : results.value()) {
        auto const& exec_receipt = exec_result.receipt;
        ASSERT_EQ(exec_receipt.status, 1u);
        ASSERT_EQ(exec_receipt.gas_used, 53'000);
    }

    // Check post-exec block state
    {
        State state{block_state, Incarnation{0, 0}};
        // ASSERT_EQ(static_cast<uint64_t>(intx::be::load<uint256_t>(state.get_balance(sender))), 0);
        ASSERT_EQ(
            intx::be::load<uint256_t>(state.get_balance(sender)),
            uint256_t{99'470'000u});
        ASSERT_EQ(state.get_nonce(sender), 26); // EVMC will inc for creation
    }
}

TEST(ExecuteBlock, multiple_tx_block_execution_succeeds)
{
    // Setup test inputs
    static constexpr auto bene{0x5353535353535353535353535353535353535353_address};
    static constexpr auto sender0{0x192cb97900c522fe1c7062c0620ebca8e6f55320_address};
    static constexpr auto sender1{0x37bafbe6f0039e4f443646481ce0066ccfac6937_address};
    static constexpr auto sender2{0x3cdd9fffcc6ee4116e8c273261464702280f83e4_address};

    // Setup objects needed (default state)
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState block_state{tdb};
    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer{};
    fiber::PriorityPool priority_pool{2, 10};

    // Setup state beforehand (inject balances, nonces etc.)
    {
        State state{block_state, Incarnation{0, 0}};
        state.add_to_balance(sender0, 100'000'000);
        state.set_nonce(sender0, 25);
        state.add_to_balance(sender1, 100'000'000);
        state.set_nonce(sender1, 234);
        state.add_to_balance(sender2, 100'000'000);
        state.set_nonce(sender2, 9);
        block_state.merge(state);
    }

    // Create a TX
    Transaction const tx0{
        .sc = {
            .r = 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
            .s = 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256
        },
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
    };

    Transaction const tx1{
        .sc = {
            .r = 0x31294533a3abd9972d30c0462dfd56fd9ebf06c87c682fd3d8548a537fbc90de_u256,
            .s = 0x4748364b61faec0e15c7ed266eb4e4e42b12b9f705f8e5a04678ce630660d02c_u256
        },
        .nonce = 234,
        .max_fee_per_gas = 10,
        .gas_limit = 149'555,
    };

    Transaction const tx2{
        .sc = {
            .r = 0xd7fef215dcdcf8f45dd3604f8da217086230644a5eb38ba2fd8389d35851196c_u256,
            .s = 0x4bb91a9042d0180f1eebbf1767626817e432e397890d2ad1f7fa245ee8684ca7_u256
        },
        .nonce = 9,
        .max_fee_per_gas = 10,
        .gas_limit = 113'158,
    };

    // Allocate state for the block
    std::vector<Transaction> transactions = {tx0, tx1, tx2};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};

    // Create the current Block of TXs / other state
    auto block = Block{
        .header = header,
        .transactions = std::move(transactions),
        .ommers = std::move(ommers),
        .withdrawals = std::move(withdrawals),
    };

    // Execute the block and modify the block state!
    auto const results = execute_block(MonadTestnet{}, rev, block, block_state, block_hash_buffer, priority_pool);

    // Check execution results
    ASSERT_TRUE(!results.has_error());

    // Check post-exec block state
    {
        State state{block_state, Incarnation{0, 0}};
        ASSERT_EQ(state.get_nonce(sender0), 26);
        ASSERT_EQ(state.get_nonce(sender1), 235);
        ASSERT_EQ(state.get_nonce(sender2), 10);
    }
}