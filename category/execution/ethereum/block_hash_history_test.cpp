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
#include <category/vm/evm/chain.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bytes32_t get_block_hash_history(State &state, uint64_t const block_number)
{
    uint256_t const index{block_number % BLOCK_HISTORY_LENGTH};
    return state.get_storage(
        BLOCK_HISTORY_ADDRESS, to_bytes(to_big_endian(index)));
}

MONAD_ANONYMOUS_NAMESPACE_END

using namespace monad;
using namespace monad::test;

using Prague = EvmChain<EVMC_PRAGUE>;

TEST(BlockHashHistory, read_write_block_hash_history_storage)
{
    static constexpr uint64_t window_size = 8191;

    // Deploy the history contract.
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
    BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
    deploy_block_hash_history_contract(state);

    // We populate the history contract with simple "hashes" for ease of
    // testing. Key: block number - 1 in big endian. Value: block number - 1 in
    // little endian. Note, special mapping: 0 -> 0.
    for (uint64_t i = 1; i <= window_size; i++) {
        BlockHeader const header{.parent_hash = to_bytes(i - 1), .number = i};
        set_block_hash_history(
            state, header); // sets `number - 1 -> to_bytes(number - 1)`
    }

    bytes32_t actual = get_block_hash_history(state, 0);
    bytes32_t expected = to_bytes(uint256_t{0});
    EXPECT_EQ(actual, expected);

    for (uint64_t i = 1; i <= window_size; i++) {
        bytes32_t actual = get_block_hash_history(state, i - 1);
        bytes32_t expected = to_bytes(i - 1);
        EXPECT_EQ(actual, expected);
    }
}

TEST(BlockHashHistory, ring_buffer)
{
    static constexpr uint64_t window_size = 8191;

    // Deploy the history contract.
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
    BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
    deploy_block_hash_history_contract(state);

    // We populate the history contract with simple "hashes" for ease of
    // testing. Key: block number - 1 in big endian. Value: block number - 1 in
    // little endian. Note, special mapping: 0 -> 0.
    // Fill it twice, causing the ring buffer to overwrite old values.
    for (uint64_t j = 0; j < 2; j++) {
        set_block_hash_history(state, header);
        for (uint64_t i = 1; i <= window_size; i++) {
            uint64_t number = window_size * j + i;
            BlockHeader const header{
                .parent_hash = to_bytes(number - 1), .number = number};
            set_block_hash_history(
                state, header); // sets `number - 1 -> to_bytes(number - 1)`
        }
    }

    // Check blocks prior to the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        bytes32_t actual = get_block_hash_history(state, i);
        bytes32_t calculated = to_bytes(i);
        EXPECT_TRUE(actual != calculated);
    }

    // Check blocks inside the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        uint64_t number = window_size + i;
        bytes32_t actual = get_block_hash_history(state, number);
        bytes32_t expected = to_bytes(number);
        EXPECT_EQ(actual, expected);
    }
}

TEST(BlockHashHistory, read_from_block_hash_history_contract)
{
    static constexpr uint64_t window_size = 8191;

    // Deploy the history contract.
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
    BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
    deploy_block_hash_history_contract(state);

    // We populate the history contract with simple "hashes" for ease of
    // testing. Key: block number - 1 in big endian. Value: block number - 1 in
    // little endian. Note, special mapping: 0 -> 0.
    // Fill it twice, causing the ring buffer to overwrite old values.
    for (uint64_t i = 1; i <= window_size; i++) {
        BlockHeader const header{.parent_hash = to_bytes(i - 1), .number = i};
        set_block_hash_history(state, header);
    }

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        // Byte encode 64 bit integers in 256 bit big endian format.
        auto const enc = [](uint64_t const x) -> bytes32_t {
            return to_bytes(to_big_endian(uint256_t{x}));
        };

        static constexpr Address history_storage_address =
            0x0000F90827F1C53a10cb7A02335B175320002935_address;

        MonadDevnet chain{};

        Transaction tx{};
        BlockHeader const header = {.number = window_size};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized buffer{};
        EvmcHost<Prague> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            chain.get_max_code_size(header.number, header.timestamp),
            chain.get_max_initcode_size(header.number, header.timestamp),
            chain.get_create_inside_delegated()};

        bytes32_t calldata = enc(block_number);
        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = history_storage_address,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = history_storage_address};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        evmc::Result result = state.vm().execute<Prague>(
            host.get_chain_params(), host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t expected = to_bytes(block_number);
            bytes32_t expected_from_state =
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

TEST(BlockHashHistory, read_write_block_hash_history_contract)
{
    static constexpr uint64_t window_size = 8191;

    // Deploy the history contract.
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
    BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
    deploy_block_hash_history_contract(state);

    // Byte encode 64 bit integers in 256 bit big endian format.
    auto const enc = [](uint64_t const x) -> bytes32_t {
        return to_bytes(to_big_endian(uint256_t{x}));
    };

    static constexpr Address history_storage_address =
        0x0000F90827F1C53a10cb7A02335B175320002935_address;

    auto const set =
        [&](uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        MonadDevnet chain{};

        Transaction tx{};
        BlockHeader const header = {.number = block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized buffer{};
        EvmcHost<Prague> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            chain.get_max_code_size(header.number, header.timestamp),
            chain.get_max_initcode_size(header.number, header.timestamp),
            chain.get_create_inside_delegated()};

        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 30'000'000,
            .recipient = history_storage_address,
            .sender = sender,
            .input_data = parent_hash.bytes,
            .input_size = 32,
            .code_address = history_storage_address};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        evmc::Result result = state.vm().execute<Prague>(
            host.get_chain_params(), host, &msg, hash, code);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    };

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            uint64_t current_block_number = 8191UL,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        MonadDevnet chain{};

        Transaction tx{};
        BlockHeader const header = {.number = current_block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized buffer{};
        EvmcHost<Prague> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            chain.get_max_code_size(header.number, header.timestamp),
            chain.get_max_initcode_size(header.number, header.timestamp),
            chain.get_create_inside_delegated()};

        bytes32_t calldata = enc(block_number);
        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = history_storage_address,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = history_storage_address};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        evmc::Result result = state.vm().execute<Prague>(
            host.get_chain_params(), host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t expected = to_bytes(block_number);
            bytes32_t expected_from_state =
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

TEST(BlockHashHistory, unauthorized_set)
{
    // Deploy the history contract.
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
    BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
    deploy_block_hash_history_contract(state);

    // Byte encode 64 bit integers in 256 bit big endian format.
    auto const enc = [](uint64_t const x) -> bytes32_t {
        return to_bytes(to_big_endian(uint256_t{x}));
    };

    static constexpr Address history_storage_address =
        0x0000F90827F1C53a10cb7A02335B175320002935_address;

    auto const set =
        [&](bool expect_success,
            uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        MonadDevnet chain{};

        Transaction tx{};
        BlockHeader const header = {.number = block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized buffer{};
        EvmcHost<Prague> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            chain.get_max_code_size(header.number, header.timestamp),
            chain.get_max_initcode_size(header.number, header.timestamp),
            chain.get_create_inside_delegated()};

        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 30'000'000,
            .recipient = history_storage_address,
            .sender = sender,
            .input_data = parent_hash.bytes,
            .input_size = 32,
            .code_address = history_storage_address};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        evmc::Result result = state.vm().execute<Prague>(
            host.get_chain_params(), host, &msg, hash, code);
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

        Transaction tx{};
        BlockHeader const header = {.number = current_block_number};
        evmc_tx_context const tx_context =
            get_tx_context<Prague>(tx, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer{};
        BlockHashBufferFinalized buffer{};
        EvmcHost<Prague> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            chain.get_max_code_size(header.number, header.timestamp),
            chain.get_max_initcode_size(header.number, header.timestamp),
            chain.get_create_inside_delegated()};

        bytes32_t calldata = enc(block_number);
        evmc_message msg{
            .kind = EVMC_CALL,
            .gas = 100'000,
            .recipient = history_storage_address,
            .sender = sender,
            .input_data = calldata.bytes,
            .input_size = 32,
            .code_address = history_storage_address};
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        evmc::Result result = state.vm().execute<Prague>(
            host.get_chain_params(), host, &msg, hash, code);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t expected = to_bytes(0xFF);
            bytes32_t expected_from_state =
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
