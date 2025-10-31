// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <optional>

using namespace monad;
using namespace monad::literals;
using namespace monad::test;

namespace
{
    uint8_t const input[] = {'i', 'n', 'p', 'u', 't'};
    uint8_t const output[] = {'o', 'u', 't', 'p', 'u', 't'};
    static Transaction const tx{.gas_limit = 10'000u};

    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;

    static constexpr std::vector<std::optional<Address>> authorities_empty{};
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

TYPED_TEST(TraitsTest, execute_success)
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
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary},
            0)(s, host);
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
        .logs = std::vector<CallFrame::Log>{},
    };

    EXPECT_EQ(call_frames[0], expected);
}

TYPED_TEST(TraitsTest, execute_reverted_insufficient_balance)
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
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary},
            0)(s, host);
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
        .logs = std::vector<CallFrame::Log>{},
    };

    EXPECT_EQ(call_frames[0], expected);
}

TYPED_TEST(TraitsTest, create_call_trace)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    // Try to deploy a contract with reverting initcode
    auto const code = 0x60fe6000526001601f6000f0_bytes;
    auto const icode = vm::make_shared_intercode(code);
    auto const code_hash = to_bytes(keccak256(code));

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max()}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = code_hash}}}}},
        Code{
            {code_hash, icode},
        },
        BlockHeader{});

    BlockState bs{tdb, vm};
    Incarnation const incarnation{0, 0};
    State s{bs, incarnation};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 1'000'000,
        .value = 0,
        .to = ADDR_B,
    };

    auto const &sender = ADDR_A;
    auto const &beneficiary = ADDR_A;

    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized buffer{};
    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary},
            0)(s, host);
    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);
    ASSERT_TRUE(call_frames.size() == 2);

    // We don't care about the specific revision-dependent gas used in each call
    // frame, only that the outer frame succeeds while the inner one fails to
    // create and has a `std::nullopt` to address.

    EXPECT_EQ(call_frames[0].type, CallType::CALL);
    EXPECT_EQ(call_frames[0].flags, 0u);
    EXPECT_EQ(call_frames[0].from, sender);
    EXPECT_EQ(call_frames[0].to, ADDR_B);
    EXPECT_EQ(call_frames[0].value, 0u);
    EXPECT_EQ(call_frames[0].input, byte_string{});
    EXPECT_EQ(call_frames[0].output, byte_string{});
    EXPECT_EQ(call_frames[0].status, EVMC_SUCCESS);
    EXPECT_EQ(call_frames[0].depth, 0u);
    EXPECT_EQ(call_frames[0].logs, std::vector<CallFrame::Log>{});

    EXPECT_EQ(call_frames[1].type, CallType::CREATE);
    EXPECT_EQ(call_frames[1].flags, 0u);
    EXPECT_EQ(call_frames[1].from, ADDR_B);
    EXPECT_EQ(call_frames[1].to, std::nullopt);
    EXPECT_EQ(call_frames[1].value, 0u);
    EXPECT_EQ(call_frames[1].input, 0xFE_bytes);
    EXPECT_EQ(call_frames[1].output, byte_string{});
    EXPECT_EQ(call_frames[1].status, EVMC_FAILURE);
    EXPECT_EQ(call_frames[1].depth, 1u);
    EXPECT_EQ(call_frames[1].logs, std::vector<CallFrame::Log>{});
}
