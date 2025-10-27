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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/block_hash_history_traits_test.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>

TEST_F(BlockHashHistoryTest, read_write_block_hash_history_storage)
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

TEST_F(BlockHashHistoryTest, ring_buffer)
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
            bytes32_t const expected = to_bytes(block_number);
            bytes32_t const expected_from_state =
                get_block_hash_history(this->state, block_number);
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
        if (i < 128) {
            EXPECT_EQ(actual, to_bytes(0xAA));
        }
        else {
            EXPECT_EQ(actual, to_bytes(0xBB));
        }
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
        EXPECT_EQ(actual, to_bytes(0xAA));
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
        EXPECT_EQ(actual, to_bytes(0xCC));
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
        if (i >= start_block - 1) {
            EXPECT_EQ(actual, to_bytes(0xAA));
        }
        else {
            EXPECT_EQ(actual, to_bytes(0xBB));
        }
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
        EXPECT_EQ(actual, to_bytes(0xAA));
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
        set_block_hash_history(
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
        EXPECT_EQ(actual, to_bytes(i + 1));
    }
}
