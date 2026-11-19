// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <memory>

using namespace monad;

// Sequential execution must merge without conflicts; an intervening storage
// write must still be detected by the node's speculative merge check.

namespace
{
    constexpr Address ACCOUNT{1};
    constexpr bytes32_t SLOT{2};

    struct MergeConflictFixture
    {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb trie_db{db};
        vm::VM vm{};
        BlockState block_state{trie_db, vm};

        MergeConflictFixture()
        {
            // Pre-state: the account exists and its slot holds 1.
            State initial_state{block_state, Incarnation{0, 0}};
            initial_state.add_to_balance(ACCOUNT, uint256_t{1000});
            initial_state.set_storage(ACCOUNT, SLOT, bytes32_t{1});
            MONAD_ASSERT(block_state.can_merge(initial_state));
            block_state.merge(initial_state);
        }
    };
}

// No intervening writer: the recorded pre-state is still current.
TEST(BlockStateCanMerge, undisturbed_state_merges)
{
    MergeConflictFixture fixture;

    State reader{fixture.block_state, Incarnation{0, 1}};
    // get_storage requires the row to be loaded; get_balance is what loads it.
    ASSERT_EQ(reader.get_balance(ACCOUNT), uint256_t{1000});
    ASSERT_EQ(reader.get_storage(ACCOUNT, SLOT), bytes32_t{1});

    EXPECT_TRUE(fixture.block_state.can_merge(reader));
}

// Use a storage conflict: account mismatches may take the relaxed-merge
// path.
TEST(BlockStateCanMerge, conflicting_write_is_detected)
{
    MergeConflictFixture fixture;

    State reader{fixture.block_state, Incarnation{0, 1}};
    ASSERT_EQ(reader.get_balance(ACCOUNT), uint256_t{1000});
    ASSERT_EQ(reader.get_storage(ACCOUNT, SLOT), bytes32_t{1});
    ASSERT_TRUE(fixture.block_state.can_merge(reader));

    // Merge a writer after the reader has observed the original slot.
    {
        State writer{fixture.block_state, Incarnation{0, 2}};
        ASSERT_EQ(writer.get_balance(ACCOUNT), uint256_t{1000});
        writer.set_storage(ACCOUNT, SLOT, bytes32_t{3});
        ASSERT_TRUE(fixture.block_state.can_merge(writer));
        fixture.block_state.merge(writer);
    }

    // The reader must retry because its recorded slot value is stale.
    EXPECT_FALSE(fixture.block_state.can_merge(reader));
}
