#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <optional>

using namespace monad;

using db_t = TrieDb;

using evmc_host_t = EvmcHost<EVMC_SHANGHAI>;

bool operator==(evmc_tx_context const &lhs, evmc_tx_context const &rhs)
{
    return !std::memcmp(
               lhs.tx_gas_price.bytes,
               rhs.tx_gas_price.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.tx_origin.bytes,
               rhs.tx_origin.bytes,
               sizeof(evmc_address)) &&
           !std::memcmp(
               lhs.block_coinbase.bytes,
               rhs.block_coinbase.bytes,
               sizeof(evmc_address)) &&
           lhs.block_number == rhs.block_number &&
           lhs.block_timestamp == rhs.block_timestamp &&
           lhs.block_gas_limit == rhs.block_gas_limit &&
           !std::memcmp(
               lhs.block_prev_randao.bytes,
               rhs.block_prev_randao.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.chain_id.bytes, rhs.chain_id.bytes, sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.block_base_fee.bytes,
               rhs.block_base_fee.bytes,
               sizeof(evmc_bytes32));
}

TEST(EvmcHost, get_tx_context)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto bene{
        0xbebebebebebebebebebebebebebebebebebebebe_address};
    static uint64_t const chain_id{1};
    static uint256_t const base_fee_per_gas{37'000'000'000};
    static uint256_t const gas_cost = 37'000'000'000;

    BlockHeader hdr{
        .prev_randao =
            0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32,
        .difficulty = 10'000'000u,
        .number = 15'000'000,
        .gas_limit = 50'000,
        .timestamp = 1677616016,
        .beneficiary = bene,
        .base_fee_per_gas = base_fee_per_gas,
    };
    Transaction const tx{
        .sc = {.chain_id = chain_id}, .max_fee_per_gas = base_fee_per_gas};

    auto const result = get_tx_context<EVMC_SHANGHAI>(tx, from, hdr, 1);
    evmc_tx_context ctx{
        .tx_origin = from,
        .block_coinbase = bene,
        .block_number = 15'000'000,
        .block_timestamp = 1677616016,
        .block_gas_limit = 50'000,
        .block_prev_randao = evmc::uint256be{10'000'000u},
    };
    intx::be::store(ctx.chain_id.bytes, uint256_t{chain_id});
    intx::be::store(ctx.tx_gas_price.bytes, gas_cost);
    intx::be::store(ctx.block_base_fee.bytes, base_fee_per_gas);
    EXPECT_EQ(result, ctx);

    hdr.difficulty = 0;
    auto const pos_result = get_tx_context<EVMC_SHANGHAI>(tx, from, hdr, 1);
    std::memcpy(
        ctx.block_prev_randao.bytes,
        hdr.prev_randao.bytes,
        sizeof(hdr.prev_randao));
    EXPECT_EQ(pos_result, ctx);
}

TEST(EvmcHost, emit_log)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto topic0{
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32};
    static constexpr auto topic1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr bytes32_t topics[] = {topic0, topic1};
    static byte_string const data = {0x00, 0x01, 0x02, 0x03, 0x04};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evmc_host_t host{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        MAX_CODE_SIZE_EIP170,
        true};

    host.emit_log(
        from,
        data.data(),
        data.size(),
        topics,
        sizeof(topics) / sizeof(bytes32_t));

    auto const logs = state.logs();
    EXPECT_EQ(logs.size(), 1);
    EXPECT_EQ(logs[0].address, from);
    EXPECT_EQ(logs[0].data, data);
    EXPECT_EQ(logs[0].topics.size(), 2);
    EXPECT_EQ(logs[0].topics[0], topic0);
    EXPECT_EQ(logs[0].topics[1], topic1);
}

TEST(EvmcHost, access_precompile)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evmc_host_t host{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        MAX_CODE_SIZE_EIP170,
        true};

    EXPECT_EQ(
        host.access_account(0x0000000000000000000000000000000000000001_address),
        EVMC_ACCESS_WARM);
    EXPECT_EQ(
        host.access_account(0x5353535353535353535353535353535353535353_address),
        EVMC_ACCESS_COLD);
}
