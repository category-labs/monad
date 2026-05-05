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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/db/witness_generator.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/vm/code.hpp>

#include <gtest/gtest.h>

#include <functional>
#include <memory>
#include <optional>
#include <utility>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr auto ADDR_A = 0x1111111111111111111111111111111111111111_address;
    constexpr auto ADDR_B = 0x2222222222222222222222222222222222222222_address;
    constexpr auto ADDR_C = 0x3333333333333333333333333333333333333333_address;

    constexpr auto SLOT_1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto SLOT_2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto SLOT_3 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto VAL_1 =
        0x000000000000000000000000000000000000000000000000000000000000abcd_bytes32;
    constexpr auto VAL_2 =
        0x000000000000000000000000000000000000000000000000000000000000beef_bytes32;
    constexpr auto VAL_3 =
        0x00000000000000000000000000000000000000000000000000000000cafef00d_bytes32;

    /// Fixture: an in-memory mpt::Db plus a TrieDb that writes to it. Tests
    /// seed the live state via commit_simple at block 0, then build a
    /// WitnessData for a synthetic block-1 delta set and round-trip it
    /// through PartialTrieDb::from_witness.
    struct WitnessGeneratorTest : public ::testing::Test
    {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};

        void apply_block(
            uint64_t block_id, StateDeltas deltas, Code const &code = {})
        {
            test::commit_simple(
                tdb,
                std::make_unique<StateDeltas>(std::move(deltas)),
                code,
                bytes32_t{2},
                BlockHeader{.number = block_id});
        }

        void seed(StateDeltas seed_deltas, Code const &seed_code = {})
        {
            apply_block(0, std::move(seed_deltas), seed_code);
            tdb.finalize(0, bytes32_t{1});
            tdb.set_block_and_prefix(0);
        }

        mpt::NodeCursor accounts_trie_cursor(uint64_t const block_number) const
        {
            auto res = db.find(
                tdb.get_root(),
                mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE),
                block_number);
            MONAD_ASSERT(res.has_value());
            return res.value();
        }

        WitnessData run_generator(
            StateDeltas const &deltas = {},
            SelfDestructStorageReads const &sd_reads = {})
        {
            return generate_witness(
                db, accounts_trie_cursor(1), 1, deltas, {}, sd_reads);
        }
    };

    PartialTrieDb partial_db_from_witness(
        bytes32_t const &pre_state_root, WitnessData const &wd)
    {
        byte_string nodes;
        for (auto const &n : wd.nodes) {
            nodes += n;
        }
        byte_string codes;
        for (auto const &c : wd.codes) {
            codes += rlp::encode_string2(byte_string_view{c.data(), c.size()});
        }
        auto ptdb = PartialTrieDb::from_witness(
            pre_state_root,
            byte_string_view{nodes.data(), nodes.size()},
            byte_string_view{codes.data(), codes.size()});
        MONAD_ASSERT(ptdb.has_value());
        return std::move(ptdb.value());
    }

    void commit_into_partial_db(
        PartialTrieDb &db, uint64_t const block_number, StateDeltas deltas)
    {
        CommitBuilder builder(block_number);
        BlockHeader header{.number = block_number};
        db.commit(
            bytes32_t{},
            builder,
            header,
            std::make_unique<StateDeltas>(std::move(deltas)),
            [](BlockHeader &) {});
    }
} // namespace

// ---------------------------------------------------------------------------
// Empty access trie: the live state root preimage is still emitted so the
// witness anchors pre_state_root. Single-account vs. multi-account exercise
// the single_branch-fusion and multi-child branches of down(INVALID_BRANCH).
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, EmptyAccessTrie_SingleAccount_EmitsStateRootLeaf)
{
    Account const acct{.balance = 100, .nonce = 1};
    seed({{ADDR_A, StateDelta{.account = {std::nullopt, acct}}}});

    bytes32_t const pre_root = tdb.state_root();

    auto const wd = run_generator();
    EXPECT_TRUE(wd.codes.empty());
    ASSERT_EQ(wd.nodes.size(), 1u);
    EXPECT_EQ(
        to_bytes(keccak256(
            byte_string_view{wd.nodes[0].data(), wd.nodes[0].size()})),
        pre_root);

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);
}

TEST_F(WitnessGeneratorTest, EmptyAccessTrie_MultiAccount_EmitsStateRootBranch)
{
    seed(
        {{ADDR_A, StateDelta{.account = {std::nullopt, Account{.nonce = 1}}}},
         {ADDR_B, StateDelta{.account = {std::nullopt, Account{.nonce = 2}}}},
         {ADDR_C, StateDelta{.account = {std::nullopt, Account{.nonce = 3}}}}});

    bytes32_t const pre_root = tdb.state_root();

    auto const wd = run_generator();
    EXPECT_TRUE(wd.codes.empty());
    ASSERT_EQ(wd.nodes.size(), 1u);
    EXPECT_EQ(
        to_bytes(keccak256(
            byte_string_view{wd.nodes[0].data(), wd.nodes[0].size()})),
        pre_root);

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);
}

// ---------------------------------------------------------------------------
// Single-child fusion: a 1-account trie exercises the section-marker fusion
// path at the root frame (single_branch=true after INVALID_BRANCH).
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, SingleAccountTrie_RootFusion_RoundTrips)
{
    Account const seed_acct{.balance = 100, .nonce = 1};
    seed({{ADDR_A, StateDelta{.account = {std::nullopt, seed_acct}}}});

    bytes32_t const pre_root = tdb.state_root();

    // Block-1 delta: bump nonce on the single existing account.
    Account const new_acct{.balance = 100, .nonce = 2};
    StateDeltas const block1_deltas{
        {ADDR_A, StateDelta{.account = {seed_acct, new_acct}}}};

    auto const wd = run_generator(block1_deltas);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);
    auto const acct = ptdb.read_account(ADDR_A);
    ASSERT_TRUE(acct.has_value());
    EXPECT_EQ(acct->nonce, seed_acct.nonce);

    // Post-commit roots must agree.
    commit_into_partial_db(ptdb, 1, block1_deltas);
    apply_block(1, block1_deltas);
    EXPECT_EQ(ptdb.state_root(), tdb.state_root());
}

// ---------------------------------------------------------------------------
// Multi-account: touching one account must emit the touched leaf and the
// untouched sibling hash so the ptdb branch is canonical.
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, TwoAccounts_TouchOne_PreservesSibling)
{
    Account const a{.balance = 1, .nonce = 1};
    Account const b{.balance = 2, .nonce = 2};
    seed(
        {{ADDR_A, StateDelta{.account = {std::nullopt, a}}},
         {ADDR_B, StateDelta{.account = {std::nullopt, b}}}});

    bytes32_t const pre_root = tdb.state_root();

    // Touch only ADDR_A: the witness must include a reference for ADDR_B.
    Account const a2{.balance = 1, .nonce = 2};
    StateDeltas const block1_deltas{{ADDR_A, StateDelta{.account = {a, a2}}}};

    auto const wd = run_generator(block1_deltas);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);
    EXPECT_EQ(ptdb.read_account(ADDR_A), a);
    // ADDR_B remains an opaque HashStub, but the trie shape must hash the
    // same as the live trie; that's what state_root() checks.
}

// ---------------------------------------------------------------------------
// Account/storage boundary: a touched slot pulls in the account leaf and
// crosses into the per-account storage trie.
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, AccountStorage_TouchedSlot_CrossesBoundary)
{
    Account const a{.balance = 10, .nonce = 1};
    seed(
        {{ADDR_A,
          StateDelta{
              .account = {std::nullopt, a},
              .storage = {{SLOT_1, {bytes32_t{}, VAL_1}}}}}});

    bytes32_t const pre_root = tdb.state_root();

    // Update the existing slot to a new value.
    StateDeltas const block1_deltas{
        {ADDR_A,
         StateDelta{.account = {a, a}, .storage = {{SLOT_1, {VAL_1, VAL_2}}}}}};

    auto const wd = run_generator(block1_deltas);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);
    EXPECT_EQ(ptdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT_1), VAL_1);

    commit_into_partial_db(ptdb, 1, block1_deltas);
    EXPECT_EQ(ptdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT_1), VAL_2);
}

// ---------------------------------------------------------------------------
// SSTORE-zero: deleting one of two sibling slots forces emission of the
// surviving sibling so the ptdb commit's trie_delete + branch compression
// match the live trie.
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, SSTOREZero_EmitsSurvivingStorageSibling)
{
    Account const a{.balance = 10, .nonce = 1};
    seed(
        {{ADDR_A,
          StateDelta{
              .account = {std::nullopt, a},
              .storage = {
                  {SLOT_1, {bytes32_t{}, VAL_1}},
                  {SLOT_2, {bytes32_t{}, VAL_2}},
                  {SLOT_3, {bytes32_t{}, VAL_3}}}}}});

    bytes32_t const pre_root = tdb.state_root();

    // Zero out SLOT_2; SLOT_1 and SLOT_3 stay live.
    StateDeltas const block1_deltas{
        {ADDR_A,
         StateDelta{
             .account = {a, a}, .storage = {{SLOT_2, {VAL_2, bytes32_t{}}}}}}};

    auto const wd = run_generator(block1_deltas);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);

    // Apply the same delta to both sides; the ptdb trie's commit must
    // produce a matching root, which can only happen if the surviving
    // sibling reference was present in the witness.
    commit_into_partial_db(ptdb, 1, block1_deltas);
    apply_block(1, block1_deltas);
    EXPECT_EQ(ptdb.state_root(), tdb.state_root());
}

// ---------------------------------------------------------------------------
// Account-level deletion (SELFDESTRUCT semantics): the witness must allow
// the ptdb commit's trie_delete to find the surviving accounts-trie
// sibling and compress the branch identically.
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, AccountDeletion_PreservesAccountsTrieSibling)
{
    Account const a{.balance = 1, .nonce = 1};
    Account const b{.balance = 2, .nonce = 1};
    Account const c{.balance = 3, .nonce = 1};
    seed(
        {{ADDR_A, StateDelta{.account = {std::nullopt, a}}},
         {ADDR_B, StateDelta{.account = {std::nullopt, b}}},
         {ADDR_C, StateDelta{.account = {std::nullopt, c}}}});

    bytes32_t const pre_root = tdb.state_root();

    // SELFDESTRUCT-style delete: (old, nullopt).
    StateDeltas const block1_deltas{
        {ADDR_A, StateDelta{.account = {a, std::nullopt}}}};

    auto const wd = run_generator(block1_deltas);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);

    commit_into_partial_db(ptdb, 1, block1_deltas);
    apply_block(1, block1_deltas);
    EXPECT_EQ(ptdb.state_root(), tdb.state_root());
}

// ---------------------------------------------------------------------------
// self_destruct_storage_reads: slots read before a SELFDESTRUCT live outside
// the StateDeltas (BlockState clears them on merge) and must be added to
// the witness via the secondary access-trie pass.
// ---------------------------------------------------------------------------

TEST_F(WitnessGeneratorTest, SelfDestructStorageReads_AppearInWitness)
{
    Account const a{.balance = 10, .nonce = 1};
    Account const b{.balance = 20, .nonce = 1};
    seed(
        {{ADDR_A,
          StateDelta{
              .account = {std::nullopt, a},
              .storage =
                  {{SLOT_1, {bytes32_t{}, VAL_1}},
                   {SLOT_2, {bytes32_t{}, VAL_2}}}}},
         {ADDR_B, StateDelta{.account = {std::nullopt, b}}}});

    bytes32_t const pre_root = tdb.state_root();

    // Block-1: ADDR_A is destroyed; its delta carries no storage entries
    // (BlockState::merge cleared them), but the slots were read before the
    // destruct and must therefore land in the witness.
    StateDeltas const block1_deltas{
        {ADDR_A, StateDelta{.account = {a, std::nullopt}}}};

    SelfDestructStorageReads sd_reads;
    sd_reads[ADDR_A].insert(SLOT_1);
    sd_reads[ADDR_A].insert(SLOT_2);

    auto const wd = run_generator(block1_deltas, sd_reads);
    ASSERT_FALSE(wd.nodes.empty());

    auto ptdb = partial_db_from_witness(pre_root, wd);
    EXPECT_EQ(ptdb.state_root(), pre_root);

    // The pre-state slot reads on ADDR_A must be answerable from the
    // ptdb trie without hitting a HashStub.
    EXPECT_EQ(ptdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT_1), VAL_1);
    EXPECT_EQ(ptdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT_2), VAL_2);
}
