#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;

using db_t = db::InMemoryTrieDB;
using traits_t = fork_traits::shanghai;

using evm_host_t = EvmcHost<traits_t::rev>;

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    db_t db;
    BlockState bs{db};
    State s{bs};

    s.add_to_balance(from, 56'000'000'000'000'000);
    s.set_nonce(from, 25);

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
        .from = from,
    };

    auto const tx_context = get_tx_context<traits_t::rev>(t, BlockHeader{});
    BlockHashBuffer const block_hash_buffer;
    evm_host_t h{tx_context, block_hash_buffer, s};

    auto result = static_validate_transaction<traits_t::rev>(t, 10u);
    EXPECT_TRUE(!result.has_error());
    result = validate_transaction(s, t);
    EXPECT_TRUE(!result.has_error());

    auto receipt = execute(s, h, t, 10u, bene);
    EXPECT_EQ(receipt.status, 1u);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(from)),
        uint256_t{55'999'999'999'470'000});
    EXPECT_EQ(s.get_nonce(from), 26); // EVMC will inc for creation

    // check if miner gets the right reward
    EXPECT_EQ(receipt.gas_used * 10u, uint256_t{530'000});
}
