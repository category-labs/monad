#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/in_memory_old_trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validation.hpp>
#include <monad/execution/validation_status.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;

using db_t = db::InMemoryOldTrieDB;
using traits_t = fork_traits::shanghai;
using processor_t = TransactionProcessor<traits_t>;

using evm_host_t = EvmcHost<traits_t>;

TEST(TransactionProcessor, g_star)
{
    static Transaction const t{
        .gas_limit = 51'000,
    };

    processor_t const p{};

    EXPECT_EQ(p.g_star(t, 1002, 15000), 11001);
    EXPECT_EQ(p.g_star(t, 1001, 15000), 11000);
    EXPECT_EQ(p.g_star(t, 1000, 15000), 11000);
    EXPECT_EQ(p.g_star(t, 999, 15000), 10999);
}

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    db_t db;
    BlockState bs;
    State s{bs, db};

    s.add_to_balance(from, 56'000'000'000'000'000);
    s.set_nonce(from, 25);

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
        .from = from,
    };

    auto const tx_context = get_tx_context<traits_t>(t, {});
    BlockHashBuffer const block_hash_buffer;
    evm_host_t h{tx_context, block_hash_buffer, s};

    processor_t const p{};

    auto status = static_validate_txn<traits_t>(t, 10u);
    if (status == ValidationStatus::SUCCESS) {
        status = validate_txn(s, t);
    }
    EXPECT_EQ(status, ValidationStatus::SUCCESS);
    auto result = p.execute(s, h, t, 10u, bene);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(from)),
        uint256_t{55'999'999'999'470'000});
    EXPECT_EQ(s.get_nonce(from), 26); // EVMC will inc for creation

    // check if miner gets the right reward
    EXPECT_EQ(result.gas_used * 10u, uint256_t{530'000});
}
