#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <optional>

using namespace monad;
using namespace monad::test;

namespace
{
    uint8_t const input[] = {'i', 'n', 'p', 'u', 't'};
    uint8_t const output[] = {'o', 'u', 't', 'p', 'u', 't'};
    static Transaction const tx{.gas_limit = 10'000u};

    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
}

TEST(CallFrame, to_json)
{
    CallFrame call_frame{
        .type = CallType::CALL,
        .from = a,
        .to = std::make_optional(b),
        .value = 20'901u,
        .gas = 100'000u,
        .gas_used = 21'000u,
        .input = byte_string{},
        .status = EVMC_SUCCESS,
    };

    auto const json_str = R"(
    {
        "from":"0x5353535353535353535353535353535353535353",
        "gas":"0x186a0",
        "gasUsed":"0x5208",
        "input":"0x",
        "to":"0xbebebebebebebebebebebebebebebebebebebebe",
        "type":"CALL",
        "value":"0x51a5",
        "depth":0, 
        "calls":[],
        "output":"0x"
    })";

    EXPECT_EQ(to_json(call_frame), nlohmann::json::parse(json_str));
}

TEST(CallTrace, enter_and_exit)
{
    evmc_message msg{.input_data = input};
    evmc::Result res{};
    res.output_data = output;

    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};
    {
        msg.depth = 0;
        call_tracer.on_enter(msg);
        {
            msg.depth = 1;
            call_tracer.on_enter(msg);
            call_tracer.on_exit(res);
        }
        call_tracer.on_exit(res);
    }

    EXPECT_EQ(call_frames.size(), 2);
    EXPECT_EQ(call_frames[0].depth, 0);
    EXPECT_EQ(call_frames[1].depth, 1);
}

TEST(CallTrace, execute_success)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x200000,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = NULL_HASH}}}}},
        Code{},
        BlockHeader{});

    BlockState bs{tdb, vm};
    Incarnation const incarnation{0, 0};
    State s{bs, incarnation};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 0x100000,
        .value = 0x10000,
        .to = ADDR_B,
    };

    auto const &sender = ADDR_A;
    auto const &beneficiary = ADDR_A;

    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized buffer{};
    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};

    // Create Call and Create executors for the host
    EthereumMainnet chain;
    Call<EVMC_SHANGHAI> call_executor{s, call_tracer, chain, 0, nullptr};
    BlockHeader header{.beneficiary = beneficiary};
    Create<EVMC_SHANGHAI> create_executor{chain, s, header, call_tracer};

    EvmcHost<EVMC_SHANGHAI> host(
        call_tracer, tx_context, buffer, s, call_executor, create_executor);

    auto const result = ExecuteTransactionNoValidation<EVMC_SHANGHAI>(
        EthereumMainnet{},
        tx,
        sender,
        BlockHeader{.beneficiary = beneficiary},
        0,
        nullptr)(s, host, call_tracer);
    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);
    ASSERT_TRUE(call_frames.size() == 1);

    CallFrame expected{
        .type = CallType::CALL,
        .flags = 0,
        .from = sender,
        .to = ADDR_B,
        .value = 0x10000,
        .gas = 0x100000,
        .gas_used = 0x5208,
        .status = EVMC_SUCCESS,
        .depth = 0,
    };

    EXPECT_EQ(call_frames[0], expected);
}

TEST(CallTrace, execute_reverted_insufficient_balance)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x10000,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = NULL_HASH}}}}},
        Code{},
        BlockHeader{});

    BlockState bs{tdb, vm};
    Incarnation const incarnation{0, 0};
    State s{bs, incarnation};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 0x10000,
        .value = 0x10000,
        .to = ADDR_B,
    };

    auto const &sender = ADDR_A;
    auto const &beneficiary = ADDR_A;

    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized buffer{};
    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};

    // Create Call and Create executors for the host
    EthereumMainnet chain;
    Call<EVMC_SHANGHAI> call_executor{s, call_tracer, chain, 0, nullptr};
    BlockHeader header{.beneficiary = beneficiary};
    Create<EVMC_SHANGHAI> create_executor{chain, s, header, call_tracer};

    EvmcHost<EVMC_SHANGHAI> host(
        call_tracer, tx_context, buffer, s, call_executor, create_executor);

    auto const result = ExecuteTransactionNoValidation<EVMC_SHANGHAI>(
        EthereumMainnet{},
        tx,
        sender,
        BlockHeader{.beneficiary = beneficiary},
        0,
        nullptr)(s, host, call_tracer);
    EXPECT_TRUE(result.status_code == EVMC_INSUFFICIENT_BALANCE);
    ASSERT_TRUE(call_frames.size() == 1);

    CallFrame expected{
        .type = CallType::CALL,
        .flags = 0,
        .from = sender,
        .to = ADDR_B,
        .value = 0x10000,
        .gas = 0x10000,
        .gas_used = 0x5208,
        .status = EVMC_INSUFFICIENT_BALANCE,
        .depth = 0,
    };

    EXPECT_EQ(call_frames[0], expected);
}
