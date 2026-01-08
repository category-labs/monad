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
#include <category/execution/monad/chain/monad_chain.hpp>
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

    static ankerl::unordered_dense::segmented_set<Address> const
        empty_grandparent_senders_and_authorities;
    static ankerl::unordered_dense::segmented_set<Address> const
        empty_parent_senders_and_authorities;
    static ankerl::unordered_dense::segmented_set<Address> const
        empty_senders_and_authorities{};
    static std::vector<Address> const empty_senders{Address{0}};
    static std::vector<std::vector<std::optional<Address>>> const
        empty_authorities{{}};

    template <typename T>
    ChainContext<T> empty_chain_ctx()
    {
        if constexpr (is_monad_trait_v<T>) {
            return ChainContext<T>{
                .grandparent_senders_and_authorities =
                    empty_grandparent_senders_and_authorities,
                .parent_senders_and_authorities =
                    empty_parent_senders_and_authorities,
                .senders_and_authorities = empty_senders_and_authorities,
                .senders = empty_senders,
                .authorities = empty_authorities};
        }
        else {
            return ChainContext<T>{};
        }
    }
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
    auto const chain_ctx = empty_chain_ctx<typename TestFixture::Trait>();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s, tx, base_fee, 0, chain_ctx};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary})(s, host);
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
    auto const chain_ctx = empty_chain_ctx<typename TestFixture::Trait>();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s, tx, base_fee, 0, chain_ctx};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary})(s, host);
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
    auto const chain_ctx = empty_chain_ctx<typename TestFixture::Trait>();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s, tx, base_fee, 0, chain_ctx};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary})(s, host);
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

TYPED_TEST(TraitsTest, selfdestruct_logs)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    // Deploy a nested contract, which then immediately selfdestructs.
    auto const code =
        evmc::from_hex(
            "0x60806040526004361061003f576000357c010000000000000000000000000000"
            "000000000000000000000000000090048063e2179b8e1461004b57610046565b36"
            "61004657005b600080fd5b34801561005757600080fd5b50610060610062565b00"
            "5b7f440a57bf0cad4531f0d64cfe9a30829810bbcd2b992d0ef6c9a6bd73bb65c5"
            "e560405160405180910390a160405161009a90610159565b604051809103906000"
            "f0801580156100b157600080fd5b5073ffffffffffffffffffffffffffffffffff"
            "ffffff166326121ff06040518163ffffffff167c01000000000000000000000000"
            "000000000000000000000000000000000281526004016000604051808303816000"
            "87803b15801561011557600080fd5b5060325a03f115801561012757600080fd5b"
            "505050507fd217144c730a1ad05c23bd421e694cff562f313468e7486c268e4930"
            "19a7829b60405160405180910390a1565b60ea806101668339019056fe60806040"
            "52348015600f57600080fd5b5060cd80601d6000396000f3fe6080604052348015"
            "600f57600080fd5b50600436106045576000357c01000000000000000000000000"
            "000000000000000000000000000000009004806326121ff014604a575b600080fd"
            "5b60506052565b005b7f6031a8d62d7c95988fa262657cd92107d90ed96e08d8f8"
            "67d32f26edfe85502260405160405180910390a13373ffffffffffffffffffffff"
            "ffffffffffffffffff16fffea26469706673582212206367043456832a7ff0e060"
            "4dde473049ca4ba64964041f92dfd8f25f0c37dafd64736f6c634300081e0033a2"
            "646970667358221220427a5624d9e1f84187016962f57b5c42f4b04d42afb5c627"
            "6904553a8a6ef61c64736f6c634300081e0033")
            .value();
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
        .data = 0xe2179b8e_bytes,
    };

    auto const &sender = ADDR_A;
    auto const &beneficiary = ADDR_A;

    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized buffer{};
    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};
    auto const chain_ctx = empty_chain_ctx<typename TestFixture::Trait>();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s, tx, base_fee, 0, chain_ctx};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary})(s, host);
    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);

    EXPECT_EQ(call_frames.size(), 4);
    EXPECT_EQ(call_frames[0].type, CallType::CALL);
    EXPECT_EQ(call_frames[1].type, CallType::CREATE);
    EXPECT_EQ(call_frames[2].type, CallType::CALL);
    EXPECT_EQ(call_frames[3].type, CallType::SELFDESTRUCT);

    for (auto const &frame : call_frames) {
        EXPECT_TRUE(frame.logs.has_value());
    }
}

// Regression test for a bug where selfdestruct call frames would be incorrectly
// grouped together at the same depth when they occur consecutively. The buggy
// behaviour is, with depths in square brackets:
//
//   [0] Create A
//   [1] ---> Create B
//   [2] ---|---> Self Destruct B
//   [2] ---|---> Self Destruct A
//
// This is incorrect, because the self-destruct of A should be a child of the
// creation of A, not the creation of B. The behaviour we want is:
//
//   [0] Create A
//   [1] ---> Create B
//   [2] ---|---> Self Destruct B
//   [1] ---> Self Destruct A
//
TYPED_TEST(TraitsTest, selfdestruct_depth)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    // Tries to deploy a contract that selfdestructs in its constructor, then
    // selfdestructs itself in the constructor. See diagram above.
    auto const initcode =
        evmc::from_hex(
            "0x6080604052348015600f57600080fd5b50604051601a906036565b6040518091"
            "03906000f080158015603057600080fd5b50329050ff5b60148060428339019056"
            "fe6080604052348015600f57600080fd5b5032fffe")
            .value();

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max()}}}}},
        Code{},
        BlockHeader{});

    BlockState bs{tdb, vm};
    Incarnation const incarnation{0, 0};
    State s{bs, incarnation};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 1'000'000,
        .value = 0,
        .to = std::nullopt,
        .data = initcode,
    };

    auto const &sender = ADDR_A;
    auto const &beneficiary = ADDR_A;

    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized buffer{};
    std::vector<CallFrame> call_frames;
    CallTracer call_tracer{tx, call_frames};
    auto const chain_ctx = empty_chain_ctx<typename TestFixture::Trait>();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer, tx_context, buffer, s, tx, base_fee, 0, chain_ctx};

    auto const result =
        ExecuteTransactionNoValidation<typename TestFixture::Trait>(
            EthereumMainnet{},
            tx,
            sender,
            authorities_empty,
            BlockHeader{.beneficiary = beneficiary})(s, host);
    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);

    EXPECT_EQ(call_frames.size(), 4);

    EXPECT_EQ(call_frames[0].type, CallType::CREATE);
    EXPECT_EQ(call_frames[0].depth, 0);

    EXPECT_EQ(call_frames[1].type, CallType::CREATE);
    EXPECT_EQ(call_frames[1].depth, 1);

    EXPECT_EQ(call_frames[2].type, CallType::SELFDESTRUCT);
    EXPECT_EQ(call_frames[2].depth, 2);

    EXPECT_EQ(call_frames[3].type, CallType::SELFDESTRUCT);
    EXPECT_EQ(call_frames[3].depth, 1);
}
