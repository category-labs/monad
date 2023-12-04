#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;

using db_t = db::InMemoryTrieDB;

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    db_t db;
    BlockState bs{db};
    State state{bs};

    state.add_to_balance(from, 56'000'000'000'000'000);
    state.set_nonce(from, 25);

    Transaction tx{
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBuffer const block_hash_buffer;

    auto const result =
        execute_impl<EVMC_SHANGHAI>(tx, from, header, block_hash_buffer, state);

    ASSERT_TRUE(!result.has_error());

    auto const &receipt = result.value();

    EXPECT_EQ(receipt.status, 1u);
    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(from)),
        uint256_t{55'999'999'999'470'000});
    EXPECT_EQ(state.get_nonce(from), 26); // EVMC will inc for creation

    // check if miner gets the right reward
    EXPECT_EQ(receipt.gas_used * 10u, uint256_t{530'000});
}
