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

#include <test/utils/db_parity_harness.hpp>

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/db.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <string>

using namespace monad;
using namespace monad::test;

namespace
{
    Address const ADDR{0xabc};
    bytes32_t const SLOT{1};

    // Commit one finalized block carrying `deltas` to a single Db, mirroring
    // commit_sequential() without depending on test_resource_data.h.
    void commit_block(
        Db &db, uint64_t const number, std::unique_ptr<StateDeltas> deltas,
        Code const &code = {})
    {
        BlockHeader const header{.number = number};
        bytes32_t const block_id{number}; // number >= 1 => non-empty block id
        commit_simple(db, std::move(deltas), code, block_id, header);
        db.finalize(number, block_id);
        db.set_block_and_prefix(number);
    }

    std::string report(BlockParity const &b)
    {
        std::string s;
        for (std::string const &m : b.mismatches) {
            s += "\n  " + m;
        }
        return s;
    }
}

// Two independent MonadDB instances fed identical inputs must agree on every
// root and sampled read, block after block.
TEST(DbParityHarness, monaddb_self_proof_matches_across_blocks)
{
    mpt::Db mdb_a{std::make_unique<InMemoryMachine>()};
    mpt::Db mdb_b{std::make_unique<InMemoryMachine>()};
    TrieDb a{mdb_a};
    TrieDb b{mdb_b};
    DbParityHarness harness{a, b, "monaddb-a", "monaddb-b"};

    SampledKey const sampled[] = {
        SampledKey::account_of(ADDR),
        SampledKey::storage_of(ADDR, Incarnation{0, 0}, SLOT)};

    auto const blk1 = harness.on_block(
        1,
        [](Db &db) {
            commit_block(
                db,
                1,
                sd(
                    {{ADDR,
                      StateDelta{
                          .account = {std::nullopt, Account{.nonce = 1}},
                          .storage = {
                              {SLOT, {bytes32_t{}, bytes32_t{0x42}}}}}}}));
        },
        sampled);
    EXPECT_TRUE(blk1.match()) << report(blk1);

    auto const blk2 = harness.on_block(
        2,
        [](Db &db) {
            commit_block(
                db,
                2,
                sd(
                    {{ADDR,
                      StateDelta{
                          .account = {
                              Account{.nonce = 1}, Account{.nonce = 2}}}}}));
        },
        sampled);
    EXPECT_TRUE(blk2.match()) << report(blk2);

    auto const blk3 = harness.on_block(
        3,
        [](Db &db) {
            commit_block(
                db,
                3,
                sd(
                    {{ADDR,
                      StateDelta{
                          .account = {Account{.nonce = 2}, std::nullopt}}}}));
        },
        sampled);
    EXPECT_TRUE(blk3.match()) << report(blk3);

    EXPECT_EQ(harness.blocks(), 3u);
    EXPECT_EQ(harness.mismatched_blocks(), 0u);
    EXPECT_TRUE(harness.ok());
}

// The harness must actually catch divergence (not just always pass): feed the
// two Dbs different account values for the same block and require a mismatch.
TEST(DbParityHarness, detects_divergence)
{
    mpt::Db mdb_a{std::make_unique<InMemoryMachine>()};
    mpt::Db mdb_b{std::make_unique<InMemoryMachine>()};
    TrieDb a{mdb_a};
    TrieDb b{mdb_b};
    DbParityHarness harness{a, b};

    commit_block(
        a,
        1,
        sd(
            {{ADDR,
              StateDelta{.account = {std::nullopt, Account{.nonce = 1}}}}}));
    commit_block(
        b,
        1,
        sd(
            {{ADDR,
              StateDelta{.account = {std::nullopt, Account{.nonce = 999}}}}}));

    SampledKey const sampled[] = {SampledKey::account_of(ADDR)};
    auto const blk = harness.compare(1, sampled);

    EXPECT_FALSE(blk.match());
    EXPECT_FALSE(harness.ok());
    // Both the state root and the sampled account read should flag.
    EXPECT_GE(blk.mismatches.size(), 2u);
}
