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

#include "fixture.hpp"

#include <category/core/runtime/uint256.hpp>
#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

namespace
{
    inline constexpr runtime::uint256_t key = 6732;
    inline constexpr runtime::uint256_t memory_offset = 0;
    inline constexpr size_t BLOCK_SIZE = 4096;
}

TYPED_TEST(RuntimeTraitsTest, PStorageLoadCold)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(pload<traits>);

    // Provide enough gas for memory expansion + cold storage access
    this->ctx_.gas_remaining = 50000;

    // pload now takes key and memory offset, writes to memory
    load(key, memory_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Verify memory was expanded to accommodate 4KB
    ASSERT_GE(this->ctx_.memory.size, BLOCK_SIZE);

    // Verify memory is zeroed (no block storage exists yet)
    bool all_zero = true;
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        if (this->ctx_.memory.data[i] != 0) {
            all_zero = false;
            break;
        }
    }
    ASSERT_TRUE(all_zero);
}

TYPED_TEST(RuntimeTraitsTest, PStorageLoadWarm)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(pload<traits>);

    this->host_.access_storage(
        this->ctx_.env.recipient, bytes32_from_uint256(key));

    // Provide gas for memory expansion and warm storage access
    this->ctx_.gas_remaining = 1000;
    load(key, memory_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Verify memory was expanded
    ASSERT_GE(this->ctx_.memory.size, BLOCK_SIZE);
}

TYPED_TEST(RuntimeTraitsTest, PStorageStoreAndLoad)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(pload<traits>);
    auto store = TestFixture::wrap(pstore<traits>);

    // Prepare memory with test data (4KB block)
    // Fill first 256 bytes with a pattern, rest with zeros
    for (size_t i = 0; i < 256; ++i) {
        this->ctx_.memory.data[i] = static_cast<uint8_t>(i & 0xFF);
    }
    for (size_t i = 256; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0;
    }
    this->ctx_.memory.size = BLOCK_SIZE;

    // Store the block with plenty of gas
    this->ctx_.gas_remaining = 50000;

    store(key, memory_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Clear memory to verify load works
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0xFF; // Fill with 0xFF
    }

    // Load the block back
    this->ctx_.gas_remaining = 5000;
    load(key, memory_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Verify the loaded data matches what we stored
    bool pattern_matches = true;
    for (size_t i = 0; i < 256; ++i) {
        if (this->ctx_.memory.data[i] != static_cast<uint8_t>(i & 0xFF)) {
            pattern_matches = false;
            break;
        }
    }
    ASSERT_TRUE(pattern_matches);

    // Verify rest is zeros
    bool rest_zero = true;
    for (size_t i = 256; i < BLOCK_SIZE; ++i) {
        if (this->ctx_.memory.data[i] != 0) {
            rest_zero = false;
            break;
        }
    }
    ASSERT_TRUE(rest_zero);
}

TYPED_TEST(RuntimeTraitsTest, PStorageMultipleBlocks)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(pload<traits>);
    auto store = TestFixture::wrap(pstore<traits>);

    // Store two different blocks at different keys (same memory offset)
    runtime::uint256_t key1 = 100;
    runtime::uint256_t key2 = 200;
    runtime::uint256_t offset =
        0; // Use same memory offset, different storage keys

    // Prepare memory with pattern 0xAA for first block
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0xAA;
    }
    this->ctx_.memory.size = BLOCK_SIZE;

    this->ctx_.gas_remaining = 50000;
    store(key1, offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Prepare memory with pattern 0xBB for second block
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0xBB;
    }

    this->ctx_.gas_remaining = 50000;
    store(key2, offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Clear memory
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0;
    }

    // Load first block
    this->ctx_.gas_remaining = 5000;
    load(key1, offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Verify first block is 0xAA
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        ASSERT_EQ(this->ctx_.memory.data[i], 0xAA);
    }

    // Clear memory again before loading second block
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        this->ctx_.memory.data[i] = 0;
    }

    // Load second block
    this->ctx_.gas_remaining = 5000;
    load(key2, offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);

    // Verify second block is 0xBB
    for (size_t i = 0; i < BLOCK_SIZE; ++i) {
        ASSERT_EQ(this->ctx_.memory.data[i], 0xBB);
    }
}

TYPED_TEST(RuntimeTraitsTest, PStorageMemoryExpansion)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(pload<traits>);
    auto store = TestFixture::wrap(pstore<traits>);

    // Test that pload/pstore properly expand memory
    runtime::uint256_t high_offset = 8192; // Start at 8KB offset

    // Initially memory should be small or empty
    size_t initial_size = this->ctx_.memory.size;

    // pload should expand memory to offset + 4KB
    this->ctx_.gas_remaining = 50000;
    load(key, high_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_GE(
        this->ctx_.memory.size, static_cast<size_t>(high_offset) + BLOCK_SIZE);

    // pstore should also handle memory expansion
    this->ctx_.memory.size = static_cast<std::uint32_t>(initial_size); // Reset
    this->ctx_.gas_remaining = 50000;
    store(key, high_offset);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_GE(
        this->ctx_.memory.size, static_cast<size_t>(high_offset) + BLOCK_SIZE);
}
