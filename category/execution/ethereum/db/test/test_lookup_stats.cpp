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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/db.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::literals;
using namespace monad::test;

namespace
{
    Address const ADDR_A =
        0x00000000000000000000000000000000000000aa_address;
    Address const ADDR_B =
        0x00000000000000000000000000000000000000bb_address;
    Address const ADDR_MISS =
        0x00000000000000000000000000000000000000ff_address;
}

TEST(LookupStats, EmptyBeforeAnyReads)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};

    auto const stats = tdb.drain_lookup_stats();
    EXPECT_EQ(stats.count, 0u);
    EXPECT_EQ(stats.max, 0u);
}

TEST(LookupStats, RecordsAccountAndStorageLookups)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};

    Account const acct_a{.balance = 1, .nonce = 1};
    Account const acct_b{.balance = 2, .nonce = 2};

    commit_simple(
        tdb,
        sd({
            {ADDR_A,
             StateDelta{.account = {std::nullopt, acct_a}, .storage = {}}},
            {ADDR_B,
             StateDelta{.account = {std::nullopt, acct_b}, .storage = {}}},
        }),
        Code{},
        bytes32_t{1},
        BlockHeader{.number = 0});

    // Drain whatever the commit itself produced -- we only care about the
    // lookups we explicitly issue below.
    (void)tdb.drain_lookup_stats();

    EXPECT_TRUE(tdb.read_account(ADDR_A).has_value());
    EXPECT_TRUE(tdb.read_account(ADDR_B).has_value());
    EXPECT_FALSE(tdb.read_account(ADDR_MISS).has_value());

    auto const stats = tdb.drain_lookup_stats();
    EXPECT_EQ(stats.count, 3u)
        << "expected exactly one record per read_account call (hit or miss)";
    EXPECT_GT(stats.max, 0u);
    EXPECT_GT(stats.mean, 0.0);
}

TEST(LookupStats, DrainResetsCounters)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};

    Account const acct{.balance = 1, .nonce = 1};
    commit_simple(
        tdb,
        sd({{ADDR_A,
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}}}),
        Code{},
        bytes32_t{1},
        BlockHeader{.number = 0});

    (void)tdb.drain_lookup_stats();
    (void)tdb.read_account(ADDR_A);
    auto const first = tdb.drain_lookup_stats();
    EXPECT_EQ(first.count, 1u);

    auto const second = tdb.drain_lookup_stats();
    EXPECT_EQ(second.count, 0u);
}
