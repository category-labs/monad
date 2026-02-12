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
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/vm/evm/delegation.hpp>
#include <monad/test/traits_test.hpp>
#include <test_resource_data.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <utility>

using namespace monad;
using namespace monad::test;

using db_t = TrieDb;

#define PUSH3(x) 0x62, (((x) >> 16) & 0xFF), (((x) >> 8) & 0xFF), ((x) & 0xFF)

TYPED_TEST(TraitsTest, create_with_insufficient)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt, Account{.balance = 10'000'000'000}}}}},
        Code{},
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };
    uint256_t const v{70'000'000'000'000'000}; // too much
    intx::be::store(m.value.bytes, v);

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};
    auto const result = create<typename TestFixture::Trait>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_INSUFFICIENT_BALANCE);
}

// Test that CREATE transactions that fail due to insufficient balance
// do not bump nonce prior to MONAD_FIVE but do bump it after
TYPED_TEST(TraitsTest, create_insufficient_balance_nonce_bump)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr uint64_t initial_nonce = 5;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .nonce = initial_nonce}}}}},
        Code{},
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message m{
        .kind = EVMC_CREATE,
        .depth = 0, // top-level transaction
        .gas = 20'000,
        .sender = from,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };
    uint256_t const v{70'000'000'000'000'000}; // too much balance required
    intx::be::store(m.value.bytes, v);

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    auto const result = create<typename TestFixture::Trait>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_INSUFFICIENT_BALANCE);

    auto const final_nonce = s.get_nonce(from);
    if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
        if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FIVE) {
            EXPECT_EQ(final_nonce, initial_nonce + 1);
        }
        else {
            EXPECT_EQ(final_nonce, initial_nonce);
        }
    }
    else {
        // Asserting expected behavior here but noting that this test is
        // unrealistic for ethereum since the sender balance is always
        // sufficient to pay for the gas + value
        EXPECT_EQ(final_nonce, initial_nonce);
    }
}

TYPED_TEST(TraitsTest, eip684_existing_code)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xd0e9eb6589febcdb3e681ba6954e881e73b3eef4_address};
    static constexpr auto code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 10'000'000'000, .nonce = 7}}}},
            {to,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash}}}}},
        Code{},
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };
    uint256_t const v{70'000'000};
    intx::be::store(m.value.bytes, v);

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};
    auto const result = create<typename TestFixture::Trait>(&h, s, m);
    EXPECT_EQ(result.status_code, EVMC_INVALID_INSTRUCTION);
}

TYPED_TEST(TraitsTest, create_nonce_out_of_range)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto new_addr{
        0x58f3f9ebd5dbdf751f12d747b02d00324837077d_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .nonce = std::numeric_limits<uint64_t>::max()}}}}},
        Code{},
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };
    uint256_t const v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = create<typename TestFixture::Trait>(&h, s, m);

    EXPECT_FALSE(s.account_exists(new_addr));
    EXPECT_EQ(result.status_code, EVMC_ARGUMENT_OUT_OF_RANGE);
}

TYPED_TEST(TraitsTest, static_precompile_execution)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000004_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    commit_sequential(
        tdb,
        StateDeltas{
            {code_address,
             StateDelta{.account = {std::nullopt, Account{.nonce = 4}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 15'000}}}}},
        Code{},
        BlockHeader{});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = 400,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity()};

    auto const result = call<typename TestFixture::Trait>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 382);
    ASSERT_EQ(result.output_size, data_size);
    EXPECT_EQ(std::memcmp(result.output_data, m.input_data, data_size), 0);
    EXPECT_NE(result.output_data, m.input_data);
}

TYPED_TEST(TraitsTest, out_of_gas_static_precompile_execution)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000001_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    commit_sequential(
        tdb,
        StateDeltas{
            {code_address,
             StateDelta{.account = {std::nullopt, Account{.nonce = 6}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 15'000}}}}},
        Code{},
        BlockHeader{});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = 100,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity()};

    evmc::Result const result = call<typename TestFixture::Trait>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_OUT_OF_GAS);
}

// Checks that the CREATE opcode respects the configured max code size for the
// current chain.
TYPED_TEST(TraitsTest, create_op_max_initcode_size)
{
    static constexpr auto good_code_address{
        0xbebebebebebebebebebebebebebebebebebebebe_address};

    static constexpr auto bad_code_address{
        0xdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdf_address};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;

    // PUSH3 max_initcode_size(); PUSH0; PUSH0; CREATE
    uint8_t const good_code[] = {
        PUSH3(TestFixture::Trait::max_initcode_size()), 0x5f, 0x5f, 0xf0};
    auto const good_icode = vm::make_shared_intercode(good_code);
    auto const good_code_hash = to_bytes(keccak256(good_code));

    // PUSH3 max_initcode_size() + 1; PUSH0; PUSH0; CREATE
    uint8_t const bad_code[] = {
        PUSH3(TestFixture::Trait::max_initcode_size() + 1), 0x5f, 0x5f, 0xf0};
    auto const bad_icode = vm::make_shared_intercode(bad_code);
    auto const bad_code_hash = to_bytes(keccak256(bad_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {good_code_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = good_code_hash,
                      }}}},
            {bad_code_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = bad_code_hash,
                      }}}},
        },
        Code{
            {good_code_hash, good_icode},
            {bad_code_hash, bad_icode},
        },
        BlockHeader{});

    BlockState bs{tdb, vm};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;

    auto s = State{bs, Incarnation{0, 0}};

    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    // Initcode fits inside size limit
    if constexpr (
        TestFixture::Trait::max_initcode_size() <
        std::numeric_limits<size_t>::max()) {
        static_assert(TestFixture::Trait::max_initcode_size() < 0xFFFFFF);
        auto msg_memory = vm.message_memory_ref();
        evmc_message m{
            .kind = EVMC_CALL,
            .gas = 1'000'000,
            .recipient = good_code_address,
            .sender = from,
            .code_address = good_code_address,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = vm.message_memory_capacity()};

        auto const result = call<typename TestFixture::Trait>(&h, s, m);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    }

    // Initcode doesn't fit inside size limit
    if constexpr (
        TestFixture::Trait::max_initcode_size() <
        std::numeric_limits<size_t>::max()) {
        auto msg_memory = vm.message_memory_ref();
        evmc_message m{
            .kind = EVMC_CALL,
            .gas = 1'000'000,
            .recipient = bad_code_address,
            .sender = from,
            .code_address = bad_code_address,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = vm.message_memory_capacity()};

        auto const result = call<typename TestFixture::Trait>(&h, s, m);
        ASSERT_EQ(result.status_code, EVMC_OUT_OF_GAS);
    }
}

// Checks that the CREATE2 opcode respects the configured max code size for the
// current chain.
TYPED_TEST(TraitsTest, create2_op_max_initcode_size)
{
    static constexpr auto good_code_address{
        0xbebebebebebebebebebebebebebebebebebebebe_address};

    static constexpr auto bad_code_address{
        0xdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdf_address};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;

    // PUSH0; PUSH3 max_initcode_size(); PUSH0; PUSH0; CREATE2
    uint8_t const good_code[] = {
        0x5f, PUSH3(TestFixture::Trait::max_initcode_size()), 0x5f, 0x5f, 0xf5};
    auto const good_icode = vm::make_shared_intercode(good_code);
    auto const good_code_hash = to_bytes(keccak256(good_code));

    // PUSH0; PUSH3 max_initcode_size() + 1; PUSH0; PUSH0; CREATE2
    uint8_t const bad_code[] = {
        0x5f,
        PUSH3(TestFixture::Trait::max_initcode_size() + 1),
        0x5f,
        0x5f,
        0xf5};
    auto const bad_icode = vm::make_shared_intercode(bad_code);
    auto const bad_code_hash = to_bytes(keccak256(bad_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {good_code_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = good_code_hash,
                      }}}},
            {bad_code_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = bad_code_hash,
                      }}}},
        },
        Code{
            {good_code_hash, good_icode},
            {bad_code_hash, bad_icode},
        },
        BlockHeader{});

    BlockState bs{tdb, vm};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;

    auto s = State{bs, Incarnation{0, 0}};

    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    // Initcode fits inside size limit
    if constexpr (
        TestFixture::Trait::max_initcode_size() <
        std::numeric_limits<size_t>::max()) {
        static_assert(TestFixture::Trait::max_initcode_size() < 0xFFFFFF);
        auto msg_memory = vm.message_memory_ref();
        evmc_message m{
            .kind = EVMC_CALL,
            .gas = 1'000'000,
            .recipient = good_code_address,
            .sender = from,
            .code_address = good_code_address,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = vm.message_memory_capacity()};

        auto const result = call<typename TestFixture::Trait>(&h, s, m);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    }

    // Initcode doesn't fit inside size limit
    if constexpr (
        TestFixture::Trait::max_initcode_size() <
        std::numeric_limits<size_t>::max()) {
        auto msg_memory = vm.message_memory_ref();
        evmc_message m{
            .kind = EVMC_CALL,
            .gas = 1'000'000,
            .recipient = bad_code_address,
            .sender = from,
            .code_address = bad_code_address,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = vm.message_memory_capacity()};

        auto const result = call<typename TestFixture::Trait>(&h, s, m);
        ASSERT_EQ(result.status_code, EVMC_OUT_OF_GAS);
    }
}

TYPED_TEST(TraitsTest, deploy_contract_code_not_enough_of_gas)
{
    static constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    commit_sequential(
        tdb,
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});
    BlockState bs{tdb, vm};

    uint8_t const code[] = {0xde, 0xad, 0xbe, 0xef};
    // Successfully deploy code
    {
        State s{bs, Incarnation{0, 0}};
        static constexpr int64_t gas = 10'000;
        evmc::Result r{EVMC_SUCCESS, gas, 0, code, sizeof(code)};
        auto const r2 = deploy_contract_code<typename TestFixture::Trait>(
            s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
        EXPECT_EQ(r2.gas_left, gas - 200 * sizeof(code));
        EXPECT_EQ(r2.create_address, a);
        auto const icode = s.get_code(a)->intercode();
        EXPECT_EQ(
            byte_string_view(icode->code(), icode->size()),
            byte_string_view(code, sizeof(code)));
    }

    {
        State s{bs, Incarnation{0, 1}};
        evmc::Result r{EVMC_SUCCESS, 700, 0, code, sizeof(code)};
        auto const r2 = deploy_contract_code<typename TestFixture::Trait>(
            s, a, std::move(r));
        EXPECT_EQ(r2.gas_left, 700);
        // Fail to deploy code - out of gas (EIP-2)
        EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
        EXPECT_EQ(r2.create_address, 0x00_address);
    }
}

TYPED_TEST(TraitsTest, deploy_contract_code_max_code_size)
{
    static constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    commit_sequential(
        tdb,
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});
    BlockState bs{tdb, vm};

    if constexpr (
        TestFixture::Trait::max_code_size() <
        std::numeric_limits<size_t>::max()) {
        uint8_t const ptr[250000]{0x00};
        byte_string code{ptr, 250000};
        static_assert(TestFixture::Trait::max_code_size() < 250000);

        State s{bs, Incarnation{0, 0}};

        evmc::Result r{
            EVMC_SUCCESS,
            std::numeric_limits<int64_t>::max(),
            0,
            code.data(),
            code.size()};
        auto const r2 = deploy_contract_code<typename TestFixture::Trait>(
            s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, 0x00_address);
    }
}

TYPED_TEST(TraitsTest, deploy_contract_code_validation)
{
    static constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    commit_sequential(
        tdb,
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});
    BlockState bs{tdb, vm};

    // EIP-3541 validation
    byte_string const illegal_code{0xef, 0x60};

    State s{bs, Incarnation{0, 0}};

    evmc::Result r{
        EVMC_SUCCESS, 1'000, 0, illegal_code.data(), illegal_code.size()};
    auto const r2 =
        deploy_contract_code<typename TestFixture::Trait>(s, a, std::move(r));
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_LONDON) {
        // Contract starting with 0xef was valid before the London revision
        EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
        EXPECT_EQ(r2.create_address, a);
    }
    else {
        EXPECT_EQ(r2.status_code, EVMC_CONTRACT_VALIDATION_FAILURE);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, 0x00_address);
    }
}

TYPED_TEST(TraitsTest, create_inside_delegated_call)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto eoa{
        0x00000000000000000000000000000000aaaaaaaa_address};

    static constexpr auto from{
        0x00000000000000000000000000000000bbbbbbbb_address};

    static constexpr auto delegated{
        0x00000000000000000000000000000000cccccccc_address};

    uint8_t eoa_code[23] = {0xEF, 0x01, 0x00};
    std::copy_n(delegated.bytes, 20, &eoa_code[3]);
    auto const eoa_icode = vm::make_shared_intercode(eoa_code);
    auto const eoa_code_hash = to_bytes(keccak256(eoa_code));

    // PUSH0; PUSH0; PUSH0; CREATE
    auto const delegated_code = evmc::from_hex("0x5F5F5FF0").value();
    auto const delegated_icode = vm::make_shared_intercode(delegated_code);
    auto const delegated_code_hash = to_bytes(keccak256(delegated_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {eoa,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = eoa_code_hash,
                      }}}},
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                      }}}},
            {delegated,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = delegated_code_hash,
                      }}}}},
        Code{
            {eoa_code_hash, eoa_icode},
            {delegated_code_hash, delegated_icode},
        },
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .flags = EVMC_DELEGATED,
        .gas = 1'000'000,
        .recipient = eoa,
        .sender = from,
        .code_address = delegated,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        auto const result = h.call(m);
        // CREATE should fail on Monad chains and succeed on Ethereum chains
        if constexpr (TestFixture::Trait::can_create_inside_delegated()) {
            static_assert(TestFixture::is_evm_trait());
            EXPECT_EQ(result.status_code, EVMC_SUCCESS);
        }
        else {
            static_assert(TestFixture::is_monad_trait());
            EXPECT_EQ(result.status_code, EVMC_FAILURE);
        }
    }
}

TYPED_TEST(TraitsTest, create2_inside_delegated_call_via_delegatecall)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    // `eoa` 7702-delegates its code to `delegated`, which makes a DELEGATECALL
    // to `creator`, which eventually tries to CREATE a contract
    static constexpr auto eoa{
        0x00000000000000000000000000000000aaaaaaaa_address};

    static constexpr auto from{
        0x00000000000000000000000000000000bbbbbbbb_address};

    static constexpr auto delegated{
        0x00000000000000000000000000000000cccccccc_address};

    static constexpr auto creator{
        0x00000000000000000000000000000000dddddddd_address};

    uint8_t eoa_code[23] = {0xEF, 0x01, 0x00};
    std::copy_n(delegated.bytes, 20, &eoa_code[3]);
    auto const eoa_icode = vm::make_shared_intercode(eoa_code);
    auto const eoa_code_hash = to_bytes(keccak256(eoa_code));

    // Make a delegatecall to the creator contract, and fail execution if that
    // call failed.
    //
    // PUSH0; PUSH0; PUSH0; PUSH0; PUSH20 creator; GAS; DELEGATECALL;
    // PUSH1 0x1f; JUMPI; INVALID; JUMPDEST[1f]
    auto const delegated_code =
        evmc::from_hex(
            "5f5f5f5f7300000000000000000000000000000000dddddddd5af4601f57fe5b")
            .value();
    auto const delegated_icode = vm::make_shared_intercode(delegated_code);
    auto const delegated_code_hash = to_bytes(keccak256(delegated_code));

    // PUSH0; PUSH0; PUSH0; PUSH0; CREATE2
    auto const creator_code = evmc::from_hex("0x5F5F5F5FF5").value();
    auto const creator_icode = vm::make_shared_intercode(creator_code);
    auto const creator_code_hash = to_bytes(keccak256(creator_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {eoa,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = eoa_code_hash,
                      }}}},
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                      }}}},
            {delegated,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = delegated_code_hash,
                      }}}},
            {creator,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = creator_code_hash,
                      }}}}},
        Code{
            {eoa_code_hash, eoa_icode},
            {delegated_code_hash, delegated_icode},
            {creator_code_hash, creator_icode},
        },
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .flags = EVMC_DELEGATED,
        .gas = 1'000'000,
        .recipient = eoa,
        .sender = from,
        .code_address = delegated,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        auto const result = h.call(m);
        // CREATE2 should fail on Monad chains and succeed on Ethereum chains
        if constexpr (TestFixture::Trait::can_create_inside_delegated()) {
            static_assert(TestFixture::is_evm_trait());
            EXPECT_EQ(result.status_code, EVMC_SUCCESS);
        }
        else {
            static_assert(TestFixture::is_monad_trait());
            EXPECT_EQ(result.status_code, EVMC_FAILURE);
        }
    }
}

TYPED_TEST(TraitsTest, nested_call_to_delegated_precompile)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    // `from` calls `contract`, which delegatecalls `eoa`, which has delegated
    // its code to a precompile.
    static constexpr auto eoa{
        0x00000000000000000000000000000000aaaaaaaa_address};

    static constexpr auto from{
        0x00000000000000000000000000000000bbbbbbbb_address};

    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};

    // Delegated to ecRecover
    auto const eoa_code =
        evmc::from_hex("0xEF01000000000000000000000000000000000000000001")
            .value();
    auto const eoa_icode = vm::make_shared_intercode(eoa_code);
    auto const eoa_code_hash = to_bytes(keccak256(eoa_code));

    // Make a delegatecall to the EOA account with 100 gas, and fail execution
    // if that call failed.
    //
    // PUSH0; PUSH0; PUSH0; PUSH0; PUSH20 eoa; PUSH1 100; DELEGATECALL;
    // PUSH1 0x20; JUMPI; INVALID; JUMPDEST[20]
    auto const contract_code =
        evmc::from_hex("5f5f5f5f7300000000000000000000000000000000aaaaaaaa6064f"
                       "4602057fe5b")
            .value();
    auto const contract_icode = vm::make_shared_intercode(contract_code);
    auto const contract_code_hash = to_bytes(keccak256(contract_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {eoa,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = eoa_code_hash,
                      }}}},
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                      }}}},
            {contract,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = contract_code_hash,
                      }}}}},
        Code{
            {eoa_code_hash, eoa_icode},
            {contract_code_hash, contract_icode},
        },
        BlockHeader{});

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = 1'000'000,
        .recipient = contract,
        .sender = from,
        .code_address = contract,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };

    // requires EIP-7702
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        BlockHashBufferFinalized const block_hash_buffer;
        NoopCallTracer call_tracer;
        Transaction tx{};
        auto const chain_ctx =
            ChainContext<typename TestFixture::Trait>::debug_empty();
        uint256_t base_fee{0};
        EvmcHost<typename TestFixture::Trait> h{
            call_tracer,
            EMPTY_TX_CONTEXT,
            block_hash_buffer,
            s,
            tx,
            base_fee,
            0,
            chain_ctx};

        auto const result = h.call(m);

        EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    }
}

TYPED_TEST(TraitsTest, cold_account_access)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x00000000000000000000000000000000bbbbbbbb_address};

    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};

    // push cold address; BALANCE
    auto const code =
        evmc::from_hex("0x7300000000000000000000000000000000aaaaaaaa31")
            .value();
    auto const icode = vm::make_shared_intercode(code);
    auto const code_hash = to_bytes(keccak256(code));

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                      }}}},
            {contract,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .code_hash = code_hash,
                      }}}}},
        Code{
            {code_hash, icode},
        },
        BlockHeader{});

    constexpr auto gas_limit = 1'000'000;

    auto msg_memory = vm.message_memory_ref();
    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = gas_limit,
        .recipient = contract,
        .sender = from,
        .code_address = contract,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};
    auto const result = h.call(m);
    auto const gas_used = gas_limit - result.gas_left;

    constexpr auto balance_gas = [] {
        if constexpr (TestFixture::is_monad_trait()) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                return 10100;
            }
            else {
                return 2600;
            }
        }
        else {
            if constexpr (TestFixture::Trait::evm_rev() >= EVMC_BERLIN) {
                return 2600;
            }
            else if constexpr (TestFixture::Trait::evm_rev() >= EVMC_ISTANBUL) {
                return 700;
            }
            else if constexpr (
                TestFixture::Trait::evm_rev() >= EVMC_TANGERINE_WHISTLE) {
                return 400;
            }
            else {
                return 20;
            }
        }
    }();

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(gas_used, balance_gas + 3); // +3 for PUSH20
}

TYPED_TEST(TraitsTest, defensive_delegation_check)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;

    static constexpr auto falsely_delegated_1{
        0x00000000000000000000000000000000aaaaaaaa_address};

    static constexpr auto falsely_delegated_2{
        0x00000000000000000000000000000000bbbbbbbb_address};

    static constexpr auto falsely_delegated_3{
        0x00000000000000000000000000000000cccccccc_address};

    static constexpr auto correctly_delegated{
        0x00000000000000000000000000000000dddddddd_address};

    uint8_t bad_code[50] = {0xEF, 0x01, 0x00, 0xFE};
    auto const bad_icode = vm::make_shared_intercode(bad_code);
    auto const bad_code_hash = to_bytes(keccak256(bad_code));

    uint8_t bad_code2[24] = {0xEF, 0x01, 0x00};
    bad_code2[23] = 0xAA;
    auto const bad_icode2 = vm::make_shared_intercode(bad_code2);
    auto const bad_code_hash2 = to_bytes(keccak256(bad_code2));

    uint8_t short_code[3] = {0xEF, 0x01, 0x00};
    auto const short_icode = vm::make_shared_intercode(short_code);
    auto const short_code_hash = to_bytes(keccak256(short_code));

    uint8_t good_code[23] = {0xEF, 0x01, 0x00};
    std::memcpy(&good_code[3], falsely_delegated_3.bytes, sizeof(Address));
    auto const good_icode = vm::make_shared_intercode(good_code);
    auto const good_code_hash = to_bytes(keccak256(good_code));

    commit_sequential(
        tdb,
        StateDeltas{
            {falsely_delegated_1,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = short_code_hash,
                      }}}},
            {falsely_delegated_2,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = bad_code_hash2,
                      }}}},
            {falsely_delegated_3,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = bad_code_hash,
                      }}}},
            {correctly_delegated,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .code_hash = good_code_hash,
                      }}}}},
        Code{
            {bad_code_hash, bad_icode},
            {bad_code_hash2, bad_icode2},
            {short_code_hash, short_icode},
            {good_code_hash, good_icode}},
        BlockHeader{});

    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    EvmcHost<typename TestFixture::Trait> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        s,
        tx,
        base_fee,
        0,
        chain_ctx};

    auto const d1 = vm::evm::resolve_delegation(
        &h.get_interface(), h.to_context(), falsely_delegated_1);
    EXPECT_FALSE(d1.has_value());
    auto const d2 = vm::evm::resolve_delegation(
        &h.get_interface(), h.to_context(), falsely_delegated_2);
    EXPECT_FALSE(d2.has_value());
    auto const d3 = vm::evm::resolve_delegation(
        &h.get_interface(), h.to_context(), falsely_delegated_3);
    EXPECT_FALSE(d3.has_value());
    auto const d4 = vm::evm::resolve_delegation(
        &h.get_interface(), h.to_context(), correctly_delegated);
    EXPECT_TRUE(d4.has_value());
    EXPECT_EQ(d4.value(), falsely_delegated_3);
}

#undef PUSH3
