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

// The Db interface over an offset-format witness trie. Node-layout and
// mutation-primitive coverage lives in test_offset_trie.cpp; this file
// exercises what PartialTrieDb adds on top — reads, commit, and the header
// accessors.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <functional>
#include <utility>

using namespace monad;

namespace
{
    // An offset-format blob with the 8-byte header and no nodes (root_off 0).
    byte_string empty_blob()
    {
        byte_string buf;
        unsigned char const magic[4] = {'M', 'Z', 'W', 0x01};
        buf.append(magic, 4);
        buf.append(4, static_cast<unsigned char>(0)); // root_off == 0
        return buf;
    }

    /// A blob whose only node is an account leaf for `addr` with an empty
    /// storage trie. Node bytes come from the production writer, so the layout
    /// has a single source of truth here as in test_offset_trie.cpp.
    byte_string account_blob(Address const &addr, Account const &acct)
    {
        byte_string buf = empty_blob();
        uint32_t const root_off = static_cast<uint32_t>(buf.size());

        auto const key = keccak256(addr.bytes);
        mpt::append_acct(buf, mpt::NULL_ID, acct, mpt::NibblesView{key});

        // LE, matching read_node_id (both sides assert a little-endian host)
        std::memcpy(buf.data() + 4, &root_off, sizeof(root_off));
        return buf;
    }

    /// PartialTrieDb holds a *view* over the node blob, so the bytes have to
    /// outlive it. Bundling the two keeps that contract local to the test.
    class TestDb
    {
        byte_string blob_;
        PartialTrieDb db_;

    public:
        explicit TestDb(byte_string blob, CodeIndex codes = {})
            : blob_(std::move(blob))
            , db_(mpt::OffsetTrie{blob_}, std::move(codes))
        {
        }

        TestDb(TestDb const &) = delete;
        TestDb &operator=(TestDb const &) = delete;

        PartialTrieDb *operator->()
        {
            return &db_;
        }
    };

    void commit_with(
        TestDb &db, BlockHeader const &header, StateDeltas deltas,
        std::function<void(BlockHeader &)> populate = [](BlockHeader &) {})
    {
        CommitBuilder builder(header.number);
        db->commit(bytes32_t{}, builder, header, deltas, std::move(populate));
    }

    /// state_root of a trie holding exactly one account, built from a blob
    /// rather than by committing — the independent oracle for commit results.
    bytes32_t single_account_root(Address const &addr, Account const &acct)
    {
        TestDb db{account_blob(addr, acct)};
        return db->state_root();
    }

    constexpr auto ADDR_X = 0x00000000000000000000000000000000deadbeef_address;
    constexpr auto ADDR_Y = 0x000000000000000000000000000000000baddcaf_address;
    constexpr auto ADDR_Z = 0xcafef00dcafef00dcafef00dcafef00dcafef00d_address;

    constexpr auto SLOT_1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto SLOT_2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto VAL_1 =
        0x000000000000000000000000000000000000000000000000000000000000abcd_bytes32;
    constexpr auto VAL_2 =
        0x000000000000000000000000000000000000000000000000000000000000beef_bytes32;
} // namespace

// ---------------------------------------------------------------------------
// Read tests
//
// Reads are served from the witness pre-state (OffsetTrie::find_original), so
// they see the blob the db was opened with, not anything a later commit built.
// ---------------------------------------------------------------------------

TEST(PartialTrieDb, Read_EmptyTrie)
{
    TestDb db{empty_blob()};
    EXPECT_EQ(db->read_account(ADDR_X), std::nullopt);
    EXPECT_EQ(db->read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), bytes32_t{});
}

TEST(PartialTrieDb, Read_LeafWitness_FoundAndAbsent)
{
    Account const acct{.balance = 1234, .nonce = 7};
    TestDb db{account_blob(ADDR_X, acct)};

    auto const found = db->read_account(ADDR_X);
    ASSERT_TRUE(found.has_value());
    EXPECT_EQ(found->balance, acct.balance);
    EXPECT_EQ(found->nonce, acct.nonce);

    // A different address misses the single leaf — the trie is fully resolved,
    // so the lookup terminates as absent rather than hitting a Digest.
    EXPECT_EQ(db->read_account(ADDR_Y), std::nullopt);
    EXPECT_EQ(db->read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), bytes32_t{});
}

TEST(PartialTrieDb, ReadCode_PresentAndMissing)
{
    byte_string const code1{
        std::initializer_list<unsigned char>{0x60, 0x01, 0x60, 0x02, 0x01}};
    byte_string const code2{std::initializer_list<unsigned char>{0x00}};
    bytes32_t const hash1 = to_bytes(keccak256(code1));
    bytes32_t const hash2 = to_bytes(keccak256(code2));

    CodeIndex codes;
    codes.emplace(hash1, vm::make_shared_intercode(code1));
    codes.emplace(hash2, vm::make_shared_intercode(code2));
    TestDb db{empty_blob(), std::move(codes)};

    auto const ic1 = db->read_code(hash1);
    EXPECT_EQ(
        byte_string_view(ic1->code(), ic1->size()), byte_string_view{code1});

    auto const ic2 = db->read_code(hash2);
    EXPECT_EQ(
        byte_string_view(ic2->code(), ic2->size()), byte_string_view{code2});

    // Missing hash returns an empty intercode rather than asserting.
    constexpr auto missing =
        0xfeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedface_bytes32;
    auto const ic_missing = db->read_code(missing);
    EXPECT_EQ(ic_missing->size(), 0u);
}

// ---------------------------------------------------------------------------
// Commit tests
//
// commit builds the post-state in the overlay; state_root() is the observable
// result, since reads stay on the pre-state blob.
// ---------------------------------------------------------------------------

TEST(PartialTrieDb, Commit_InsertSingleAccount)
{
    TestDb db{empty_blob()};
    Account const acct{.balance = 1'000, .nonce = 3};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct}}}});

    EXPECT_EQ(db->state_root(), single_account_root(ADDR_X, acct));
    EXPECT_EQ(db->get_block_number(), 1u);
}

TEST(PartialTrieDb, Commit_UpdateExistingAccount)
{
    Account const acct1{.balance = 100, .nonce = 1};
    Account const acct2{.balance = 200, .nonce = 2};

    TestDb db{account_blob(ADDR_X, acct1)};
    bytes32_t const root_before = db->state_root();

    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct1, acct2}}}});

    EXPECT_NE(db->state_root(), root_before);
    EXPECT_EQ(db->state_root(), single_account_root(ADDR_X, acct2));
}

TEST(PartialTrieDb, Commit_DeleteAccount_LeavesEmptyTrie)
{
    Account const acct{.balance = 999, .nonce = 5};
    TestDb db{account_blob(ADDR_X, acct)};
    ASSERT_NE(db->state_root(), NULL_ROOT);

    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct, std::nullopt}}}});

    EXPECT_EQ(db->state_root(), NULL_ROOT);
}

TEST(PartialTrieDb, Commit_TwoAccountsThenDeleteOne_BranchCompresses)
{
    TestDb db{empty_blob()};
    Account const acct_x{.balance = 1, .nonce = 1};
    Account const acct_y{.balance = 2, .nonce = 2};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X, StateDelta{.account = {std::nullopt, acct_x}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, acct_y}}}});
    ASSERT_NE(db->state_root(), NULL_ROOT);

    // Deleting ADDR_X must collapse the branch back to a single leaf, i.e. to
    // the same trie a witness holding only ADDR_Y would produce.
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct_x, std::nullopt}}}});

    EXPECT_EQ(db->state_root(), single_account_root(ADDR_Y, acct_y));
}

TEST(PartialTrieDb, Commit_TouchOnlyIsNoOp)
{
    Account const acct{.balance = 7, .nonce = 1};
    TestDb db{account_blob(ADDR_X, acct)};
    bytes32_t const root_before = db->state_root();

    // {nullopt, nullopt} hits neither the upsert nor the deletion pass — a
    // pure no-op, even for entries that name a present account.
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{
            {ADDR_X, StateDelta{.account = {std::nullopt, std::nullopt}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, std::nullopt}}}});

    EXPECT_EQ(db->state_root(), root_before);
}

TEST(PartialTrieDb, Commit_DeleteAbsentAccountIsNoOp)
{
    Account const acct{.balance = 7, .nonce = 1};
    TestDb db{account_blob(ADDR_X, acct)};
    bytes32_t const root_before = db->state_root();

    // ADDR_Y is not in the trie, so the deletion pass finds nothing to erase
    // and the root must be unchanged.
    Account const stale{.balance = 99};
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_Y, StateDelta{.account = {stale, std::nullopt}}}});

    EXPECT_EQ(db->state_root(), root_before);
}

TEST(PartialTrieDb, Commit_StorageInsertReadDelete)
{
    TestDb db{empty_blob()};
    Account const acct{.balance = 1, .nonce = 1};

    // Insert the account with two storage slots.
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {
                     {SLOT_1, {bytes32_t{}, VAL_1}},
                     {SLOT_2, {bytes32_t{}, VAL_2}}}}}});
    bytes32_t const root_two_slots = db->state_root();
    EXPECT_NE(root_two_slots, single_account_root(ADDR_X, acct));

    // Update SLOT_1 and delete SLOT_2 in a second commit.
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {
                     {SLOT_1, {VAL_1, VAL_2}},
                     {SLOT_2, {VAL_2, bytes32_t{}}}}}}});
    EXPECT_NE(db->state_root(), root_two_slots);

    // Deleting the surviving slot too must return the account to an empty
    // storage trie, i.e. the storage_root it had before any slot was set.
    commit_with(
        db,
        BlockHeader{.number = 3},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{SLOT_1, {VAL_2, bytes32_t{}}}}}}});
    EXPECT_EQ(db->state_root(), single_account_root(ADDR_X, acct));
}

TEST(PartialTrieDb, Commit_StorageZeroToZeroIsNoOp)
{
    TestDb db{empty_blob()};
    Account const acct{.balance = 1, .nonce = 1};

    // {0, 0} storage delta hits neither the upsert pass (sdelta.second is
    // zero) nor the delete pass (sdelta.first is zero) — pure no-op, so the
    // account lands with an empty storage trie.
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{SLOT_1, {bytes32_t{}, bytes32_t{}}}}}}});

    EXPECT_EQ(db->state_root(), single_account_root(ADDR_X, acct));
}

TEST(PartialTrieDb, Commit_PopulatesHeaderRoots)
{
    TestDb db{empty_blob()};

    constexpr auto receipts =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_bytes32;
    constexpr auto txns =
        0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb_bytes32;
    constexpr auto withdrawals =
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc_bytes32;

    commit_with(
        db, BlockHeader{.number = 42}, StateDeltas{}, [&](BlockHeader &h) {
            h.receipts_root = receipts;
            h.transactions_root = txns;
            h.withdrawals_root = withdrawals;
        });

    EXPECT_EQ(db->receipts_root(), receipts);
    EXPECT_EQ(db->transactions_root(), txns);
    ASSERT_TRUE(db->withdrawals_root().has_value());
    EXPECT_EQ(*db->withdrawals_root(), withdrawals);

    // commit_simple-style consumers expect the populated header to be readable
    // back through read_eth_header.
    auto const stored = db->read_eth_header();
    EXPECT_EQ(stored.number, 42u);
    EXPECT_EQ(stored.receipts_root, receipts);
    EXPECT_EQ(stored.transactions_root, txns);
    ASSERT_TRUE(stored.withdrawals_root.has_value());
    EXPECT_EQ(*stored.withdrawals_root, withdrawals);

    EXPECT_EQ(db->get_block_number(), 42u);
}

TEST(PartialTrieDb, SetBlockAndPrefix_UpdatesBlockNumber)
{
    TestDb db{empty_blob()};
    EXPECT_EQ(db->get_block_number(), 0u);
    db->set_block_and_prefix(99, bytes32_t{});
    EXPECT_EQ(db->get_block_number(), 99u);
}

TEST(PartialTrieDb, Commit_StateRootMatchesIndependentlyEncodedTrie)
{
    // Round-trip check: committing one account into an empty trie yields the
    // same state_root as opening a single-leaf blob directly.
    TestDb live{empty_blob()};
    Account const acct{.balance = 0xdeadbeef, .nonce = 12};
    commit_with(
        live,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_Z, StateDelta{.account = {std::nullopt, acct}}}});

    EXPECT_EQ(live->state_root(), single_account_root(ADDR_Z, acct));
}
