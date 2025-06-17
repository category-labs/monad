#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

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

    CallTracer call_tracer{tx};
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

    auto const call_frames = std::move(call_tracer).get_frames();
    EXPECT_EQ(call_frames.size(), 2);
    EXPECT_EQ(call_frames[0].depth, 0);
    EXPECT_EQ(call_frames[1].depth, 1);
}

TEST(CallTrace, execute_success)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};

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

    BlockState bs{tdb};
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
    CallTracer call_tracer{tx};
    EvmcHost<EVMC_SHANGHAI> host(
        call_tracer, tx_context, buffer, s, MAX_CODE_SIZE_EIP170, true);

    auto const result = execute_impl_no_validation<EVMC_SHANGHAI>(
        s, host, tx, sender, 1, beneficiary, MAX_CODE_SIZE_EIP170);
    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);

    auto const call_frames = std::move(call_tracer).get_frames();

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

    BlockState bs{tdb};
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
    CallTracer call_tracer{tx};
    EvmcHost<EVMC_SHANGHAI> host(
        call_tracer, tx_context, buffer, s, MAX_CODE_SIZE_EIP170, true);

    auto const result = execute_impl_no_validation<EVMC_SHANGHAI>(
        s, host, tx, sender, 1, beneficiary, MAX_CODE_SIZE_EIP170);
    EXPECT_TRUE(result.status_code == EVMC_INSUFFICIENT_BALANCE);

    auto const call_frames = std::move(call_tracer).get_frames();

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
