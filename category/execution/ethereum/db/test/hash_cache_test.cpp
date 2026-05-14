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
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/hash_cache.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstdint>
#include <optional>

using namespace monad;
using namespace monad::test;
using namespace monad::literals;

namespace
{
    constexpr auto ADDR_X = 0x0000000000000000000000000000000000000001_address;
    constexpr auto ADDR_Y = 0x0000000000000000000000000000000000000002_address;
    constexpr auto ADDR_Z = 0x0000000000000000000000000000000000000003_address;

    struct HashCacheFixture : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
    };
}

// Baseline parity: with no deltas, applying compute_state_root after
// prefetching the touched accounts should yield exactly the on-disk root.
TEST_F(HashCacheFixture, NoOpDeltaMatchesOnDiskStateRoot)
{
    TrieDb tdb{this->db};

    // Commit a few accounts (no storage) at block 0.
    Account const a{.balance = 100, .nonce = 1};
    Account const b{.balance = 200, .nonce = 2};
    Account const c{.balance = 300, .nonce = 3};
    commit_sequential(
        tdb,
        sd({{ADDR_X, StateDelta{.account = {std::nullopt, a}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, b}}},
            {ADDR_Z, StateDelta{.account = {std::nullopt, c}}}}),
        Code{},
        BlockHeader{.number = 0});

    bytes32_t const pre_state_root = tdb.state_root();
    auto const on_disk_root = tdb.get_root();
    auto const state_prefix = mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE);

    HashCache hc;
    hc.reset(pre_state_root);
    hc.prefetch_account(
        this->db,
        on_disk_root,
        mpt::NibblesView{state_prefix},
        tdb.get_block_number(),
        ADDR_X);
    hc.prefetch_account(
        this->db,
        on_disk_root,
        mpt::NibblesView{state_prefix},
        tdb.get_block_number(),
        ADDR_Y);
    hc.prefetch_account(
        this->db,
        on_disk_root,
        mpt::NibblesView{state_prefix},
        tdb.get_block_number(),
        ADDR_Z);

    // Empty deltas: the post-state must equal the pre-state.
    StateDeltas const empty_deltas;
    EXPECT_EQ(hc.compute_state_root(empty_deltas), pre_state_root);
}

// Storage stub preservation: when the touched account has storage and only
// its balance changes, the per-account storage subtree stays as a HashStub
// initialized to the account's canonical storage_root. The final state root
// must still match what TrieDb produces.
TEST_F(HashCacheFixture, BalanceUpdateOnAccountWithStorage)
{
    TrieDb tdb{this->db};

    constexpr auto slot1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto slot2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto val1 =
        0x00000000000000000000000000000000000000000000000000000000deadbeef_bytes32;
    constexpr auto val2 =
        0x000000000000000000000000000000000000000000000000000000000badc0de_bytes32;

    Account const a0{.balance = 100, .nonce = 1};
    Account const b{.balance = 200, .nonce = 2};
    commit_sequential(
        tdb,
        sd({{ADDR_X,
             StateDelta{
                 .account = {std::nullopt, a0},
                 .storage =
                     {{slot1, {bytes32_t{}, val1}},
                      {slot2, {bytes32_t{}, val2}}}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, b}}}}),
        Code{},
        BlockHeader{.number = 0});

    bytes32_t const pre_state_root = tdb.state_root();
    auto const pre_on_disk_root = tdb.get_root();
    auto const state_prefix = mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE);
    uint64_t const block_number = tdb.get_block_number();

    HashCache hc;
    hc.reset(pre_state_root);
    hc.prefetch_account(
        this->db,
        pre_on_disk_root,
        mpt::NibblesView{state_prefix},
        block_number,
        ADDR_X);

    // Bump X's balance with NO storage change.
    Account const a1{.balance = 999, .nonce = 1};
    StateDeltas const deltas{
        {ADDR_X, StateDelta{.account = {a0, a1}, .storage = {}}}};
    bytes32_t const cached_root = hc.compute_state_root(deltas);

    commit_sequential(
        tdb,
        sd({{ADDR_X, StateDelta{.account = {a0, a1}, .storage = {}}}}),
        Code{},
        BlockHeader{.number = 1});
    bytes32_t const expected_root = tdb.state_root();

    EXPECT_EQ(cached_root, expected_root);
}

// Single-account update: with the touched account prefetched,
// compute_state_root applied to a balance-bump delta should equal what TrieDb
// produces when the same delta is committed.
TEST_F(HashCacheFixture, BalanceUpdateMatchesTrieDbStateRoot)
{
    TrieDb tdb{this->db};

    Account const a0{.balance = 100, .nonce = 1};
    Account const b{.balance = 200, .nonce = 2};
    Account const c{.balance = 300, .nonce = 3};
    commit_sequential(
        tdb,
        sd({{ADDR_X, StateDelta{.account = {std::nullopt, a0}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, b}}},
            {ADDR_Z, StateDelta{.account = {std::nullopt, c}}}}),
        Code{},
        BlockHeader{.number = 0});

    bytes32_t const pre_state_root = tdb.state_root();
    auto const pre_on_disk_root = tdb.get_root();
    auto const state_prefix = mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE);
    uint64_t const block_number = tdb.get_block_number();

    // Pre-compute the HashCache state root for an X-balance bump.
    HashCache hc;
    hc.reset(pre_state_root);
    hc.prefetch_account(
        this->db,
        pre_on_disk_root,
        mpt::NibblesView{state_prefix},
        block_number,
        ADDR_X);

    Account const a1{.balance = 999, .nonce = 1};
    StateDeltas const deltas{
        {ADDR_X, StateDelta{.account = {a0, a1}, .storage = {}}}};
    bytes32_t const cached_root = hc.compute_state_root(deltas);

    // Now commit the same delta via TrieDb at block 1 and read the resulting
    // state root from disk for ground truth.
    commit_sequential(
        tdb,
        sd({{ADDR_X, StateDelta{.account = {a0, a1}, .storage = {}}}}),
        Code{},
        BlockHeader{.number = 1});
    bytes32_t const expected_root = tdb.state_root();

    EXPECT_EQ(cached_root, expected_root);
}
