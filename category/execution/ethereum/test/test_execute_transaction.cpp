#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/tx_context.hpp>

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
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

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

    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    auto const result = ExecuteTransaction<EVMC_SHANGHAI>(
        EthereumMainnet{},
        0,
        tx,
        from,
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev)();

    ASSERT_TRUE(!result.has_error());

    auto const &receipt = result.value().receipt;

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
