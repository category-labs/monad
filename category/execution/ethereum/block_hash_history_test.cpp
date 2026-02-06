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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>

using namespace monad;
using namespace monad::test;

using Prague = EvmTraits<EVMC_PRAGUE>;

namespace
{
    // Byte encode 64 bit integers in 256 bit big endian format.
    bytes32_t enc(uint64_t const x)
    {
        return to_bytes(to_big_endian(uint256_t{x}));
    }

    struct BlockHistoryFixture : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;
        BlockState block_state;
        State state;
        BlockHashBufferFinalized block_hash_buffer;
        static constexpr Address blockhash_opcode_addr =
            0x00000000000000000000000000000000000123_address;

        BlockHistoryFixture()
            : db{machine}
            , tdb{db}
            , block_state{tdb, vm}
            , state{block_state, Incarnation{0, 0}}
            , block_hash_buffer{}
        {
        }

        evmc::Result call_blockhash_opcode(
            uint64_t const, uint64_t const,
            Address sender =
                0xcccccccccccccccccccccccccccccccccccccccc_address);
        void deploy_history_contract();
        void deploy_contract_that_uses_blockhash();
        void fill_history(uint64_t const, uint64_t const);
        void
        fill_history_fixed(uint64_t const, uint64_t const, bytes32_t const &);
    };

    evmc::Result BlockHistoryFixture::call_blockhash_opcode(
        uint64_t const block_number, uint64_t const current_block_number,
        Address sender)
    {
        MonadDevnet const chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = current_block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer,
            tx_context,
            block_hash_buffer,
            state,
            tx,
            base_fee,
            0,
            chain_ctx};

        bytes32_t const calldata = enc(block_number);
        auto msg_memory = state.vm().message_memory_ref();
        evmc_message const msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = blockhash_opcode_addr,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = blockhash_opcode_addr,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        return state.vm().execute<Prague>(host, &msg, hash, code);
    }

    void BlockHistoryFixture::deploy_history_contract()
    {
        BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
        deploy_block_hash_history_contract<Prague>(state);
    }

    void BlockHistoryFixture::fill_history(
        uint64_t const start_block, uint64_t const end_block)
    {
        // We populate the history contract with simple "hashes" for ease of
        // testing. Key: block number - 1 in big endian. Value: block number - 1
        // in little endian. Note, special mapping: 0 -> 0.
        for (uint64_t i = start_block; i <= end_block; i++) {
            BlockHeader const header{
                .parent_hash = to_bytes(i - 1), .number = i};
            set_block_hash_history<Prague>(
                state, header); // sets `number - 1 -> to_bytes(number - 1)`
        }
    }

    void BlockHistoryFixture::fill_history_fixed(
        uint64_t const start_block, uint64_t const end_block,
        bytes32_t const &fixed_hash)
    {
        for (uint64_t i = start_block; i <= end_block; i++) {
            BlockHeader const header{.parent_hash = fixed_hash, .number = i};
            set_block_hash_history<Prague>(
                state, header); // sets `number - 1 -> fixed_hash`
        }
    }

    void BlockHistoryFixture::deploy_contract_that_uses_blockhash()
    {
        // Deploy test contract
        using namespace monad::vm::utils;

        // execute `blockhash <block number from calldata>`
        auto eb = evm_as::prague();
        eb.push0()
            .calldataload()
            .blockhash()
            .push0()
            .mstore()
            .push(0x20)
            .push0()
            .return_();
        std::vector<uint8_t> bytecode{};
        ASSERT_TRUE(evm_as::validate(eb));
        evm_as::compile(eb, bytecode);

        byte_string_view const bytecode_view{bytecode.data(), bytecode.size()};

        // Deploy test contract
        static constexpr Address test_addr =
            0x0000000000000000000000000000000000000123_address;
        state.create_contract(test_addr);
        state.set_code(test_addr, bytecode_view);
        state.set_nonce(test_addr, 1);
    }
}

TEST_F(BlockHistoryFixture, read_write_block_hash_history_storage)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    deploy_history_contract();
    fill_history(1, window_size);

    bytes32_t const actual = get_block_hash_history(state, 0);
    bytes32_t const expected = to_bytes(uint256_t{0});
    EXPECT_EQ(actual, expected);

    for (uint64_t i = 1; i <= window_size; i++) {
        bytes32_t const actual = get_block_hash_history(state, i - 1);
        bytes32_t const expected = to_bytes(i - 1);
        EXPECT_EQ(actual, expected);
    }
}

TEST_F(BlockHistoryFixture, ring_buffer)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    deploy_history_contract();
    // Fill the history with more data than the size of the serve window,
    // causing the ring buffer to overwrite old values.
    fill_history(1, window_size * 2);

    // Check blocks prior to the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        bytes32_t const actual = get_block_hash_history(state, i);
        bytes32_t const calculated = to_bytes(i);
        EXPECT_TRUE(actual != calculated);
    }

    // Check blocks inside the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        uint64_t number = window_size + i;
        bytes32_t const actual = get_block_hash_history(state, number);
        bytes32_t const expected = to_bytes(number);
        EXPECT_EQ(actual, expected);
    }
}

TEST_F(BlockHistoryFixture, read_from_block_hash_history_contract)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    deploy_history_contract();
    fill_history(1, window_size);

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        MonadDevnet chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = window_size};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized const buffer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer, tx_context, buffer, state, tx, base_fee, 0, chain_ctx};

        bytes32_t const calldata = enc(block_number);
        auto msg_memory = state.vm().message_memory_ref();
        evmc_message const msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = BLOCK_HISTORY_ADDRESS,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = BLOCK_HISTORY_ADDRESS,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        evmc::Result const result =
            state.vm().execute<Prague>(host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected = to_bytes(block_number);
            bytes32_t const expected_from_state =
                get_block_hash_history(state, block_number);
            bytes32_t actual;
            memcpy(actual.bytes, result.output_data, 32);
            ASSERT_EQ(actual, expected);
            ASSERT_EQ(actual, expected_from_state);
        }
        else {
            ASSERT_EQ(result.status_code, EVMC_REVERT);
        }
    };

    // Values inside the serve window.
    for (uint64_t i = 0; i < window_size; i++) {
        get(true, i);
    }

    // Try some values outside the serve window.
    get(false, window_size);
    get(false, 1234567890);
}

TEST_F(BlockHistoryFixture, read_write_block_hash_history_contract)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    deploy_history_contract();

    auto const set =
        [&](uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        MonadDevnet const chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized const buffer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer, tx_context, buffer, state, tx, base_fee, 0, chain_ctx};

        auto msg_memory = state.vm().message_memory_ref();
        evmc_message const msg{
            .kind = EVMC_CALL,
            .gas = 30'000'000,
            .recipient = BLOCK_HISTORY_ADDRESS,
            .sender = sender,
            .input_data = parent_hash.bytes,
            .input_size = 32,
            .code_address = BLOCK_HISTORY_ADDRESS,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        evmc::Result const result =
            state.vm().execute<Prague>(host, &msg, hash, code);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    };

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            uint64_t current_block_number = BLOCK_HISTORY_LENGTH,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        MonadDevnet const chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = current_block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized const buffer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer, tx_context, buffer, state, tx, base_fee, 0, chain_ctx};

        bytes32_t const calldata = enc(block_number);
        auto msg_memory = state.vm().message_memory_ref();
        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = BLOCK_HISTORY_ADDRESS,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = BLOCK_HISTORY_ADDRESS,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        evmc::Result const result =
            state.vm().execute<Prague>(host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected = to_bytes(block_number);
            bytes32_t const expected_from_state =
                get_block_hash_history(state, block_number);
            bytes32_t actual;
            memcpy(actual.bytes, result.output_data, 32);
            EXPECT_EQ(actual, expected);
            EXPECT_EQ(actual, expected_from_state);
        }
        else {
            ASSERT_EQ(result.status_code, EVMC_REVERT);
        }
    };

    // We populate the history contract with simple "hashes" for ease of
    // testing. Key: block number - 1 in big endian. Value: block number - 1 in
    // little endian. Note, special mapping: 0 -> 0.
    for (uint64_t i = 1; i <= window_size; i++) {
        set(i, to_bytes(i - 1));
    }

    // Values inside the serve window.
    for (uint64_t i = 0; i < window_size; i++) {
        get(true, i);
    }

    // Fill the buffer again, partially.
    for (uint64_t i = 0; i < window_size / 2; i++) {
        uint64_t number = window_size + i;
        set(number, to_bytes(number - 1));
    }

    // Values inside the serve window.
    {
        uint64_t current_block_number = window_size + (window_size / 2);
        for (uint64_t i = 0; i < window_size; i++) {
            if (i < window_size / 2) {
                uint64_t number = window_size + i;
                get(true, number - 1, current_block_number);
            }
            else {
                get(true, i, current_block_number);
            }
        }
    }
}

TEST_F(BlockHistoryFixture, unauthorized_set)
{
    deploy_history_contract();

    auto const set =
        [&](bool expect_success,
            uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        MonadDevnet const chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized const buffer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer, tx_context, buffer, state, tx, base_fee, 0, chain_ctx};

        auto msg_memory = state.vm().message_memory_ref();
        evmc_message const msg{
            .kind = EVMC_CALL,
            .gas = 30'000'000,
            .recipient = BLOCK_HISTORY_ADDRESS,
            .sender = sender,
            .input_data = parent_hash.bytes,
            .input_size = 32,
            .code_address = BLOCK_HISTORY_ADDRESS,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        evmc::Result result =
            state.vm().execute<Prague>(host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        }
        else {
            ASSERT_EQ(result.status_code, EVMC_REVERT);
        }
    };

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            uint64_t current_block_number = 255UL,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        MonadDevnet chain{};

        Transaction const tx{};
        BlockHeader const header = {.number = current_block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized const buffer{};

        ChainContext<Prague> chain_ctx{};
        uint256_t base_fee{0};
        EvmcHost<Prague> host{
            call_tracer, tx_context, buffer, state, tx, base_fee, 0, chain_ctx};

        bytes32_t const calldata = enc(block_number);
        auto msg_memory = state.vm().message_memory_ref();
        evmc_message const msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = BLOCK_HISTORY_ADDRESS,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = BLOCK_HISTORY_ADDRESS,
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = state.vm().message_memory_capacity()};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const code = state.read_code(hash);
        evmc::Result const result =
            state.vm().execute<Prague>(host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected = to_bytes(0xFF);
            bytes32_t const expected_from_state =
                get_block_hash_history(state, block_number);
            bytes32_t actual;
            memcpy(actual.bytes, result.output_data, 32);
            EXPECT_EQ(actual, expected);
            EXPECT_EQ(actual, expected_from_state);
        }
        else {
            ASSERT_EQ(result.status_code, EVMC_REVERT);
        }
    };

    // Fill some of the history with fixed 0xFF hashes.
    for (uint64_t i = 1; i <= 256; i++) {
        set(true, i, to_bytes(0xFF));
    }

    // Unauthorized set within window.
    get(true, 42);
    set(false,
        42,
        to_bytes(0xC0FFEE),
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address);
    get(true, 42);

    // Unauthorized set outside the window.
    get(false, 512, 255);
    set(false,
        512,
        to_bytes(0xC0FFEE),
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address);
    get(false, 512, 255);
}

TEST_F(BlockHistoryFixture, get_history_undeployed)
{
    EXPECT_FALSE(state.account_exists(BLOCK_HISTORY_ADDRESS));
    EXPECT_EQ(get_block_hash_history(state, 42), bytes32_t{});
}

TEST_F(BlockHistoryFixture, blockhash_opcode)
{
    deploy_history_contract();
    deploy_contract_that_uses_blockhash();

    for (uint64_t i = 0; i < 256; i++) {
        block_hash_buffer.set(i, to_bytes(0xBB));
    }

    // Initially the storage of the block history contract will be empty.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xBB));
    }

    // Fill some of the block history.
    fill_history_fixed(0, 128, to_bytes(0xAA));

    // Since the history has less than 256 entries, we still expect to do some
    // reads from the block hash buffer.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        if (i < 128) {
            EXPECT_EQ(actual, to_bytes(0xAA));
        }
        else {
            EXPECT_EQ(actual, to_bytes(0xBB));
        }
    }

    // Fill enough entries to direct all reads to the block history
    // storage.
    fill_history_fixed(128, 256, to_bytes(0xAA));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xAA));
    }

    // Fill up the history storage a few times.
    fill_history_fixed(257, BLOCK_HISTORY_LENGTH * 3, to_bytes(0xCC));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xCC));
    }

    // Check that the semantics of `blockhash` is unaltered.
    for (uint64_t i = 256; i < BLOCK_HISTORY_LENGTH; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        bytes32_t const expected{};
        EXPECT_EQ(actual, expected);
    }
}

TEST_F(BlockHistoryFixture, blockhash_opcode_late_deploy)
{
    deploy_history_contract();
    deploy_contract_that_uses_blockhash();

    for (uint64_t i = 0; i < 256; i++) {
        block_hash_buffer.set(i, to_bytes(0xBB));
    }

    // Initially the storage of the block history contract will be empty.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xBB));
    }

    // Initialize part of the history storage, in particular the 255th slot.
    uint64_t const start_block = 256;
    fill_history_fixed(start_block, start_block + 128, to_bytes(0xAA));

    // Since the history has less than 256 entries, we still expect to do some
    // reads from the block hash buffer.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        if (i >= start_block - 1) {
            EXPECT_EQ(actual, to_bytes(0xAA));
        }
        else {
            EXPECT_EQ(actual, to_bytes(0xBB));
        }
    }

    // Fill enough entries to direct all reads to the block history
    // storage.
    fill_history_fixed(0, start_block, to_bytes(0xAA));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xAA));
    }
}

TEST_F(BlockHistoryFixture, blockhash_opcode_buffer_history_agreement)
{
    deploy_history_contract();
    deploy_contract_that_uses_blockhash();

    // Identity mapping
    for (uint64_t i = 0; i < 256; i++) {
        block_hash_buffer.set(
            i, to_bytes(i + 1)); // i + 1 to avoid throw on zero.
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(i + 1));
    }

    // Reset
    block_hash_buffer = BlockHashBufferFinalized{};
    for (uint64_t i = 0; i < 256; i++) {
        block_hash_buffer.set(i, bytes32_t{0xFF});
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, bytes32_t{0xFF});
    }

    // Identity mapping again
    for (uint64_t i = 0; i < 256; i++) {
        set_block_hash_history<Prague>(
            state,
            BlockHeader{.parent_hash = to_bytes(i + 1), .number = i + 1});
        // i + 1, because set_block_hash_history sets i - 1.
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(i + 1));
    }
}
