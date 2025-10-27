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
#include <monad/test/traits_test.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>

using namespace monad;
using namespace monad::test;

namespace
{
    // Byte encode 64 bit integers in 256 bit big endian format.
    bytes32_t enc(uint64_t const x)
    {
        return to_bytes(to_big_endian(uint256_t{x}));
    }

    struct BlockHashHistoryTest : public ::testing::Test
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

        BlockHashHistoryTest()
            : db{machine}
            , tdb{db}
            , block_state{tdb, vm}
            , state{block_state, Incarnation{0, 0}}
            , block_hash_buffer{}
        {
        }
    };

    template <typename T>
    struct BlockHashHistoryTraitsTest : public BlockHashHistoryTest
    {
        static constexpr auto get_trait()
        {
            if constexpr (std::
                              same_as<typename T::value_type, monad_revision>) {
                return monad::MonadTraits<T::value>{};
            }
            else {
                return monad::EvmTraits<T::value>{};
            }
        }

        using Trait = decltype(get_trait());

        evmc::Result call(
            uint64_t const current_block_number, Address sender,
            Address code_addr, std::uint8_t const *input_data,
            std::uint32_t input_size, int64_t gas,
            BlockHashBufferFinalized const &buffer)
        {
            MonadDevnet const chain{};

            Transaction const tx{};
            BlockHeader const header = {.number = current_block_number};
            evmc_tx_context const tx_context =
                get_tx_context<Trait>(tx, sender, header, chain.get_chain_id());
            NoopCallTracer call_tracer{};
            EvmcHost<Trait> host{call_tracer, tx_context, buffer, state};

            evmc_message const msg{
                .kind = EVMC_CALL,
                .gas = gas,
                .recipient = code_addr,
                .sender = sender,
                .input_data = input_data,
                .input_size = input_size,
                .code_address = code_addr};
            auto const hash = state.get_code_hash(msg.code_address);
            auto const &code = state.read_code(hash);
            return state.vm().template execute<Trait>(host, &msg, hash, code);
        }

        evmc::Result call_blockhash_opcode(
            uint64_t const block_number, uint64_t const current_block_number,
            Address sender = 0xcccccccccccccccccccccccccccccccccccccccc_address)
        {
            auto const calldata = enc(block_number);
            auto const input_size = 32;
            return call(
                current_block_number,
                sender,
                blockhash_opcode_addr,
                calldata.bytes,
                input_size,
                100'000,
                block_hash_buffer);
        }

        void deploy_history_contract()
        {
            BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
            deploy_block_hash_history_contract<Trait>(state);
        }

        void deploy_contract_that_uses_blockhash()
        {
            // Deploy test contract
            using namespace monad::vm::utils;

            // execute `blockhash <block number from calldata>`
            auto eb = evm_as::EvmBuilder<Trait>{};
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

            byte_string_view const bytecode_view{
                bytecode.data(), bytecode.size()};
            bytes32_t const code_hash = to_bytes(keccak256(bytecode_view));

            // Deploy test contract
            state.create_contract(blockhash_opcode_addr);
            state.set_code_hash(blockhash_opcode_addr, code_hash);
            state.set_code(blockhash_opcode_addr, bytecode_view);
            state.set_nonce(blockhash_opcode_addr, 1);
        }

        void fill_history(uint64_t const start_block, uint64_t const end_block)
        {
            // We populate the history contract with simple "hashes" for ease of
            // testing. Key: block number - 1 in big endian.
            // Value: block number - 1 in little endian.
            // Note, special mapping: 0 -> 0.
            for (uint64_t i = start_block; i <= end_block; i++) {
                BlockHeader const header{
                    .parent_hash = to_bytes(i - 1), .number = i};
                set_block_hash_history<Trait>(
                    state, header); // sets `number - 1 -> to_bytes(number - 1)`
            }
        }

        void fill_history_fixed(
            uint64_t const start_block, uint64_t const end_block,
            bytes32_t const &fixed_hash)
        {
            for (uint64_t i = start_block; i <= end_block; i++) {
                BlockHeader const header{
                    .parent_hash = fixed_hash, .number = i};
                set_block_hash_history<Trait>(
                    state, header); // sets `number - 1 -> fixed_hash`
            }
        }
    };

}

TYPED_TEST_SUITE(
    BlockHashHistoryTraitsTest,
    ::detail::MonadEvmRevisionTypesSince<EVMC_PRAGUE>,
    ::detail::RevisionTestNameGenerator);

TYPED_TEST(BlockHashHistoryTraitsTest, read_write_block_hash_history_storage)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    TestFixture::deploy_history_contract();
    TestFixture::fill_history(1, window_size);

    bytes32_t const actual = get_block_hash_history(this->state, 0);
    bytes32_t const expected = to_bytes(uint256_t{0});
    EXPECT_EQ(actual, expected);

    for (uint64_t i = 1; i <= window_size; i++) {
        bytes32_t const actual = get_block_hash_history(this->state, i - 1);
        auto const expected = [i] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return bytes32_t{};
                }
            }
            return to_bytes(i - 1);
        }();
        ASSERT_EQ(actual, expected);
        EXPECT_EQ(actual, expected);
    }
}

TYPED_TEST(BlockHashHistoryTraitsTest, ring_buffer)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    TestFixture::deploy_history_contract();
    // Fill the history with more data than the size of the serve window,
    // causing the ring buffer to overwrite old values.
    TestFixture::fill_history(1, window_size * 2);

    // Check blocks prior to the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        bytes32_t const actual = get_block_hash_history(this->state, i);
        bytes32_t const calculated = to_bytes(i);

        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                // before MONAD_SIX, nothing was being written.
                ASSERT_EQ(actual, bytes32_t{});
                continue;
            }
        }
        ASSERT_NE(actual, calculated);
    }

    // Check blocks inside the current window.
    for (uint64_t i = 0; i < window_size; i++) {
        uint64_t number = window_size + i;
        bytes32_t const actual = get_block_hash_history(this->state, number);
        auto const expected = [number] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return bytes32_t{};
                }
            }
            return to_bytes(number);
        }();
        ASSERT_EQ(actual, expected);
    }
}

TYPED_TEST(BlockHashHistoryTraitsTest, read_from_block_hash_history_contract)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    TestFixture::deploy_history_contract();
    TestFixture::fill_history(1, window_size);

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        BlockHashBufferFinalized const buffer{};

        bytes32_t const calldata = enc(block_number);
        evmc::Result const result = TestFixture::call(
            window_size,
            sender,
            BLOCK_HISTORY_ADDRESS,
            calldata.bytes,
            32,
            100'000,
            buffer);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected_from_state =
                get_block_hash_history(this->state, block_number);
            bytes32_t actual;
            memcpy(actual.bytes, result.output_data, 32);
            auto const expected = [block_number] {
                if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                    if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                        return bytes32_t{};
                    }
                }
                return to_bytes(block_number);
            }();
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

TYPED_TEST(BlockHashHistoryTraitsTest, read_write_block_hash_history_contract)
{
    static constexpr uint64_t window_size = BLOCK_HISTORY_LENGTH;

    TestFixture::deploy_history_contract();

    auto const set =
        [&](uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        BlockHashBufferFinalized const buffer{};
        evmc::Result const result = TestFixture::call(
            block_number,
            sender,
            BLOCK_HISTORY_ADDRESS,
            parent_hash.bytes,
            32,
            30'000'000,
            buffer);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    };

    auto const get =
        [&](bool expect_success,
            uint64_t block_number,
            uint64_t current_block_number = BLOCK_HISTORY_LENGTH,
            Address sender =
                0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address) -> void {
        BlockHashBufferFinalized const buffer{};

        bytes32_t const calldata = enc(block_number);
        evmc::Result const result = TestFixture::call(
            current_block_number,
            sender,
            BLOCK_HISTORY_ADDRESS,
            calldata.bytes,
            32,
            100'000,
            buffer);
        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected = to_bytes(block_number);
            bytes32_t const expected_from_state =
                get_block_hash_history(this->state, block_number);
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
    // testing. Key: block number - 1 in big endian. Value: block number - 1
    // in little endian. Note, special mapping: 0 -> 0.
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

TYPED_TEST(BlockHashHistoryTraitsTest, unauthorized_set)
{
    TestFixture::deploy_history_contract();

    auto const set =
        [&](bool expect_success,
            uint64_t block_number,
            bytes32_t parent_hash,
            Address sender =
                0xfffffffffffffffffffffffffffffffffffffffe_address) -> void {
        BlockHashBufferFinalized const buffer{};

        evmc::Result result = TestFixture::call(
            block_number,
            sender,
            BLOCK_HISTORY_ADDRESS,
            parent_hash.bytes,
            32,
            30'000'000,
            buffer);
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
        BlockHashBufferFinalized const buffer{};
        bytes32_t const calldata = enc(block_number);
        evmc::Result const result = TestFixture::call(
            current_block_number,
            sender,
            BLOCK_HISTORY_ADDRESS,
            calldata.bytes,
            32,
            100'000,
            buffer);

        if (expect_success) {
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 32);
            bytes32_t const expected = to_bytes(0xFF);
            bytes32_t const expected_from_state =
                get_block_hash_history(this->state, block_number);
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

TEST_F(BlockHashHistoryTest, get_history_undeployed)
{
    EXPECT_FALSE(state.account_exists(BLOCK_HISTORY_ADDRESS));
    EXPECT_EQ(get_block_hash_history(state, 42), bytes32_t{});
}

TYPED_TEST(BlockHashHistoryTraitsTest, blockhash_opcode)
{
    TestFixture::deploy_history_contract();
    TestFixture::deploy_contract_that_uses_blockhash();

    for (uint64_t i = 0; i < 256; i++) {
        this->block_hash_buffer.set(i, to_bytes(0xBB));
    }

    // Initially the storage of the block history contract will be empty.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xBB));
    }

    // Fill some of the block history.
    TestFixture::fill_history_fixed(0, 128, to_bytes(0xAA));

    // Since the history has less than 256 entries, we still expect to do
    // some reads from the block hash buffer.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        auto const expected = [i] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return to_bytes(0xBB);
                }
            }
            return i < 128 ? to_bytes(0xAA) : to_bytes(0xBB);
        }();
        ASSERT_EQ(actual, expected);
    }

    // Fill enough entries to direct all reads to the block history
    // storage.
    TestFixture::fill_history_fixed(128, 256, to_bytes(0xAA));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        auto const expected = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return to_bytes(0xBB);
                }
            }
            return to_bytes(0xAA);
        }();
        ASSERT_EQ(actual, expected);
    }

    // Fill up the history storage a few times.
    TestFixture::fill_history_fixed(
        257, BLOCK_HISTORY_LENGTH * 3, to_bytes(0xCC));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        auto const expected = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return to_bytes(0xBB);
                }
            }
            return to_bytes(0xCC);
        }();
        ASSERT_EQ(actual, expected);
    }

    // Check that the semantics of `blockhash` is unaltered.
    for (uint64_t i = 256; i < BLOCK_HISTORY_LENGTH; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        bytes32_t const expected{};
        EXPECT_EQ(actual, expected);
    }
}

TYPED_TEST(BlockHashHistoryTraitsTest, blockhash_opcode_late_deploy)
{
    TestFixture::deploy_history_contract();
    TestFixture::deploy_contract_that_uses_blockhash();

    for (uint64_t i = 0; i < 256; i++) {
        this->block_hash_buffer.set(i, to_bytes(0xBB));
    }

    // Initially the storage of the block history contract will be empty.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(0xBB));
    }

    // Initialize part of the history storage, in particular the 255th slot.
    uint64_t const start_block = 256;
    TestFixture::fill_history_fixed(
        start_block, start_block + 128, to_bytes(0xAA));

    // Since the history has less than 256 entries, we still expect to do
    // some reads from the block hash buffer.
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);

        auto const expected = [i] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return to_bytes(0xBB);
                }
            }
            return i >= start_block - 1 ? to_bytes(0xAA) : to_bytes(0xBB);
        }();
        ASSERT_EQ(actual, expected);
    }

    // Fill enough entries to direct all reads to the block history
    // storage.
    TestFixture::fill_history_fixed(0, start_block, to_bytes(0xAA));
    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        auto const expected = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return to_bytes(0xBB);
                }
            }
            return to_bytes(0xAA);
        }();
        ASSERT_EQ(actual, expected);
    }
}

TYPED_TEST(
    BlockHashHistoryTraitsTest, blockhash_opcode_buffer_history_agreement)
{
    TestFixture::deploy_history_contract();
    TestFixture::deploy_contract_that_uses_blockhash();

    // Identity mapping
    for (uint64_t i = 0; i < 256; i++) {
        this->block_hash_buffer.set(
            i, to_bytes(i + 1)); // i + 1 to avoid throw on zero.
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, to_bytes(i + 1));
    }

    // Reset
    this->block_hash_buffer = BlockHashBufferFinalized{};
    for (uint64_t i = 0; i < 256; i++) {
        this->block_hash_buffer.set(i, bytes32_t{0xFF});
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        EXPECT_EQ(actual, bytes32_t{0xFF});
    }

    // Identity mapping again
    for (uint64_t i = 0; i < 256; i++) {
        set_block_hash_history<typename TestFixture::Trait>(
            this->state,
            BlockHeader{.parent_hash = to_bytes(i + 1), .number = i + 1});
        // i + 1, because set_block_hash_history sets i - 1.
    }

    for (uint64_t i = 0; i < 256; i++) {
        auto const result = TestFixture::call_blockhash_opcode(i, 256);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 32);
        bytes32_t actual{};
        memcpy(actual.bytes, result.output_data, 32);
        auto const expected = [i] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                // before MONAD_SIX, the block_hash_history contract is not
                // deployed, so we read values from the block_hash_buffer
                if constexpr (TestFixture::Trait::monad_rev() < MONAD_SIX) {
                    return bytes32_t{0xFF};
                }
            }
            return to_bytes(i + 1);
        }();
        ASSERT_EQ(actual, expected);
    }
}
