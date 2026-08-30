// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <memory>

using namespace monad;

// `can_merge` is the node's optimistic-merge conflict detector. A transaction executes before its
// predecessor has merged, so the pre-state it read may already be stale by the time it wants to
// merge; can_merge compares what the State recorded as original against what the BlockState now
// holds, and the caller re-executes when they disagree.
//
// The zkVM guest declines that check through SequentialExecutionToken, on the grounds that its own
// loop merges each transaction before constructing the next State and nothing else writes the
// BlockState. That argument is only worth anything while can_merge really does fail when a writer
// DOES intervene -- an always-true predicate would make the guest's skip look justified for the
// wrong reason. These two tests pin both directions.

namespace
{
    constexpr Address ACCOUNT{1};
    constexpr bytes32_t SLOT{2};

    struct Fixture
    {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm{};
        BlockState bs{tdb, vm};

        Fixture()
        {
            // Pre-state: the account exists and its slot holds 1.
            State seed{bs, Incarnation{0, 0}};
            seed.add_to_balance(ACCOUNT, uint256_t{1000});
            seed.set_storage(ACCOUNT, SLOT, bytes32_t{1});
            MONAD_ASSERT(bs.can_merge(seed));
            bs.merge(seed);
        }
    };
}

// The direction the guest relies on: with no other writer between a State's reads and its merge,
// can_merge holds. This is the property SequentialExecutionToken asserts, stated as a test rather
// than as a comment.
TEST(BlockStateCanMerge, undisturbed_state_merges)
{
    Fixture f;

    State a{f.bs, Incarnation{0, 1}};
    // get_storage requires the row to be loaded; get_balance is what loads it.
    ASSERT_EQ(a.get_balance(ACCOUNT), uint256_t{1000});
    ASSERT_EQ(a.get_storage(ACCOUNT, SLOT), bytes32_t{1});

    EXPECT_TRUE(f.bs.can_merge(a));
}

// The direction that makes the check load-bearing on the node: a writer commits between A's read
// and A's merge, and can_merge says so. A conflict on STORAGE and not on the account is
// deliberate -- an account mismatch takes can_merge's relaxed-merge path, which repairs rather
// than refuses, so it would not exercise the refusal at all.
TEST(BlockStateCanMerge, conflicting_write_is_detected)
{
    Fixture f;

    State a{f.bs, Incarnation{0, 1}};
    ASSERT_EQ(a.get_balance(ACCOUNT), uint256_t{1000});
    ASSERT_EQ(a.get_storage(ACCOUNT, SLOT), bytes32_t{1});
    ASSERT_TRUE(f.bs.can_merge(a));

    // B is the concurrent writer: it changes the slot A read, and merges first.
    {
        State b{f.bs, Incarnation{0, 2}};
        ASSERT_EQ(b.get_balance(ACCOUNT), uint256_t{1000});
        b.set_storage(ACCOUNT, SLOT, bytes32_t{3});
        ASSERT_TRUE(f.bs.can_merge(b));
        f.bs.merge(b);
    }

    // A's recorded pre-state no longer matches the block state, and this is the whole reason the
    // node re-executes rather than merging.
    EXPECT_FALSE(f.bs.can_merge(a));
}
