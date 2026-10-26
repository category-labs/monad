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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/vm.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <memory>
#include <optional>

using namespace monad;
using namespace monad::test;
using namespace monad::literals;
using namespace monad::partitioned;

namespace
{
    bytes32_t slot(uint64_t const n)
    {
        return store_be_as<bytes32_t>(uint256_t{n});
    }

    // header slot 5, storage zone slots in two groups, and a hashed slot
    bytes32_t const header_slot = slot(5);
    bytes32_t const zone_slot = slot(1000);
    bytes32_t const zone_slot_same_group = slot(1001); // same page
    bytes32_t const hashed_slot =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    bytes32_t const value1 =
        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
    bytes32_t const value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;

    struct PartitionedInMemoryFixture : public ::testing::Test
    {
        static constexpr bool cached = false;

        static mpt::Db make_db()
        {
            return mpt::Db{std::make_unique<PartitionedInMemoryMachine>()};
        }

        mpt::Db db{make_db()};
    };

    struct PartitionedOnDiskFixture : public ::testing::Test
    {
        static constexpr bool cached = false;

        static mpt::Db make_db()
        {
            return mpt::Db{
                std::make_unique<PartitionedOnDiskMachine>(),
                mpt::OnDiskDbConfig{}};
        }

        mpt::Db db{make_db()};
    };

    struct PartitionedOnDiskCachedFixture : public PartitionedOnDiskFixture
    {
        static constexpr bool cached = true;
    };

    template <typename Fixture>
    struct PartitionedDbTest : public Fixture
    {
        TrieDb make_tdb()
        {
            return TrieDb{this->db, Fixture::cached};
        }

        // Whether a leaf exists at `key` under the finalized state table
        bool has_leaf(TrieDb const &tdb, mpt::Nibbles const &key)
        {
            return this->db
                .find(
                    tdb.get_root(),
                    mpt::concat(
                        FINALIZED_NIBBLE, STATE_NIBBLE, mpt::NibblesView{key}),
                    tdb.get_block_number())
                .has_value();
        }
    };

    using Fixtures = ::testing::Types<
        PartitionedInMemoryFixture, PartitionedOnDiskFixture,
        PartitionedOnDiskCachedFixture>;
    TYPED_TEST_SUITE(PartitionedDbTest, Fixtures);
}

TYPED_TEST(PartitionedDbTest, account_roundtrip_and_leaves)
{
    TrieDb tdb = this->make_tdb();
    EXPECT_TRUE(tdb.is_partitioned());
    EXPECT_FALSE(tdb.is_page_encoded());

    Account const acct{
        .balance = 1'000'000,
        .code_hash = A_CODE_HASH,
        .nonce = 1337,
        .incarnation = Incarnation{3, 7}};
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {std::nullopt, acct}}}}),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    EXPECT_EQ(tdb.read_account(ADDR_A), acct);
    EXPECT_EQ(tdb.read_account(ADDR_B), std::nullopt);
    auto const icode = tdb.read_code(A_CODE_HASH);
    EXPECT_EQ(byte_string_view(icode->code(), icode->size()), A_CODE);

    EXPECT_TRUE(this->has_leaf(tdb, header_stem_nibbles(ADDR_A)));
    // the account is one childless leaf at its stem key, the stem is its path
    {
        auto const res = this->db.find(
            tdb.get_root(),
            mpt::concat(
                FINALIZED_NIBBLE,
                STATE_NIBBLE,
                mpt::NibblesView{header_stem_nibbles(ADDR_A)}),
            tdb.get_block_number());
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value().node->number_of_children(), 0u);
        EXPECT_TRUE(res.value().node->data().empty());
    }
    EXPECT_FALSE(
        this->has_leaf(tdb, header_key_nibbles(ADDR_A, BASIC_DATA_LEAF_KEY)));
    EXPECT_FALSE(
        this->has_leaf(tdb, header_key_nibbles(ADDR_A, CODE_HASH_LEAF_KEY)));
    EXPECT_FALSE(tdb.storage_bucket_exists(ADDR_A));
    EXPECT_NE(tdb.state_root(), NULL_ROOT);

    // nonce and balance change rewrites basic data only
    Account acct2 = acct;
    acct2.nonce = 1338;
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {acct, acct2}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_account(ADDR_A), acct2);
}

TYPED_TEST(PartitionedDbTest, empty_account_has_a_leaf)
{
    TrieDb tdb = this->make_tdb();
    Account const empty{.incarnation = Incarnation{1, 1}};
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {std::nullopt, empty}}}}),
        Code{},
        BlockHeader{.number = 0});
    EXPECT_EQ(tdb.read_account(ADDR_A), empty);
    EXPECT_TRUE(this->has_leaf(tdb, header_stem_nibbles(ADDR_A)));

    Account funded = empty;
    funded.balance = 5;
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {empty, funded}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_account(ADDR_A), funded);

    // back to empty: the leaf stays, the account stays
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {funded, empty}}}}),
        Code{},
        BlockHeader{.number = 2});
    EXPECT_EQ(tdb.read_account(ADDR_A), empty);
    EXPECT_TRUE(this->has_leaf(tdb, header_stem_nibbles(ADDR_A)));
}

TYPED_TEST(PartitionedDbTest, storage_header_and_zone)
{
    TrieDb tdb = this->make_tdb();
    Account const acct{.nonce = 1, .incarnation = Incarnation{0, 0}};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{header_slot, {bytes32_t{}, value1}},
                       {zone_slot, {bytes32_t{}, value2}},
                       {hashed_slot, {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, header_slot), value1);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, zone_slot), value2);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, hashed_slot), value1);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, acct.incarnation, zone_slot_same_group),
        bytes32_t{});
    EXPECT_EQ(
        tdb.read_storage(ADDR_B, acct.incarnation, zone_slot), bytes32_t{});

    // the header slot lives inside the account leaf, the others are storage
    // zone leaves
    EXPECT_FALSE(this->has_leaf(
        tdb, header_key_nibbles(ADDR_A, HEADER_STORAGE_OFFSET + 5)));
    EXPECT_EQ(
        tdb.read_storage_page(ADDR_A, acct.incarnation, HEADER_PAGE_KEY)[5],
        value1);
    EXPECT_TRUE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, zone_slot)));
    EXPECT_TRUE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, hashed_slot)));
    EXPECT_TRUE(tdb.storage_bucket_exists(ADDR_A));
    EXPECT_FALSE(tdb.storage_bucket_exists(ADDR_B));

    // modify one, add one in the same group, delete one
    bytes32_t const root0 = tdb.state_root();
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, acct},
                  .storage =
                      {{zone_slot, {value2, value1}},
                       {zone_slot_same_group, {bytes32_t{}, value2}},
                       {hashed_slot, {value1, bytes32_t{}}},
                       {header_slot, {value1, value1}}}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, zone_slot), value1);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, acct.incarnation, zone_slot_same_group),
        value2);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, acct.incarnation, hashed_slot), bytes32_t{});
    EXPECT_FALSE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, hashed_slot)));
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, header_slot), value1);
    EXPECT_NE(tdb.state_root(), root0);

    // erase the header slot too
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, acct},
                  .storage = {{header_slot, {value1, bytes32_t{}}}}}}}),
        Code{},
        BlockHeader{.number = 2});
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, acct.incarnation, header_slot), bytes32_t{});
    EXPECT_TRUE(tdb.read_storage_page(ADDR_A, acct.incarnation, HEADER_PAGE_KEY)
                    .is_empty());
    EXPECT_EQ(tdb.read_account(ADDR_A), acct);
}

// After BlockState reads an account from a partitioned db, its header slots
// are answered from the account entry: the db sees no storage read
TYPED_TEST(PartitionedDbTest, block_state_serves_header_slots_with_account)
{
    TrieDb tdb = this->make_tdb();
    Account const acct{.balance = 1, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{slot(3), {bytes32_t{}, value1}},
                       {zone_slot, {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});
    (void)tdb.print_stats(); // reset the counters

    vm::VM vm;
    BlockState bs{tdb, vm};
    EXPECT_EQ(bs.read_account(ADDR_A), acct);
    EXPECT_EQ(bs.read_storage(ADDR_A, acct.incarnation, slot(3)), value1);
    EXPECT_EQ(bs.read_storage(ADDR_A, acct.incarnation, slot(9)), bytes32_t{});
    // Without a DbCache the trie sees one account read and no storage read;
    // the zone slot then costs one. With a cache the commit primed it and
    // nothing reaches the trie.
    if constexpr (!TypeParam::cached) {
        EXPECT_THAT(
            tdb.print_stats(),
            ::testing::HasSubstr(",ae=   0,ane=   1,sz=   0,snz=   0"));
    }
    EXPECT_EQ(bs.read_storage(ADDR_A, acct.incarnation, zone_slot), value2);
    if constexpr (!TypeParam::cached) {
        EXPECT_THAT(
            tdb.print_stats(),
            ::testing::HasSubstr(",ae=   0,ane=   0,sz=   0,snz=   1"));
    }
    // an absent account has no header page and no storage
    EXPECT_EQ(bs.read_account(ADDR_B), std::nullopt);
    auto const absent = tdb.read_account_and_header(ADDR_B);
    EXPECT_FALSE(absent.account.has_value());
    EXPECT_FALSE(absent.header_storage.has_value());
    auto const present = tdb.read_account_and_header(ADDR_A);
    EXPECT_EQ(present.account, acct);
    ASSERT_TRUE(present.header_storage.has_value());
    EXPECT_EQ((*present.header_storage)[3], value1);
}

TYPED_TEST(PartitionedDbTest, header_slots_and_fields_share_the_leaf)
{
    TrieDb tdb = this->make_tdb();
    Account const acct{.balance = 1, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{slot(0), {bytes32_t{}, value1}},
                       {slot(63), {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    // an account field change keeps the header slots
    Account richer = acct;
    richer.balance = 2;
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {acct, richer}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_account(ADDR_A), richer);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(0)), value1);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(63)), value2);

    // a header slot change keeps the account fields and the other slots
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {richer, richer},
                  .storage =
                      {{slot(0), {value1, bytes32_t{}}},
                       {slot(7), {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 2});
    EXPECT_EQ(tdb.read_account(ADDR_A), richer);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(0)), bytes32_t{});
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(7)), value1);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(63)), value2);
    auto const page =
        tdb.read_storage_page(ADDR_A, acct.incarnation, HEADER_PAGE_KEY);
    EXPECT_EQ(page.size(), 2u);
    EXPECT_EQ(page[7], value1);
    EXPECT_EQ(page[63], value2);
    // the whole header is the one leaf
    EXPECT_TRUE(this->has_leaf(tdb, header_stem_nibbles(ADDR_A)));
    EXPECT_FALSE(this->has_leaf(
        tdb, header_key_nibbles(ADDR_A, HEADER_STORAGE_OFFSET + 7)));

    // the header ends at slot 127; slot 128 is a storage zone leaf
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {richer, richer},
                  .storage =
                      {{slot(127), {bytes32_t{}, value2}},
                       {slot(128), {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 3});
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(127)), value2);
    EXPECT_EQ(tdb.read_storage(ADDR_A, acct.incarnation, slot(128)), value1);
    EXPECT_EQ(
        tdb.read_storage_page(ADDR_A, acct.incarnation, HEADER_PAGE_KEY)[127],
        value2);
    EXPECT_TRUE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, slot(128))));
    EXPECT_TRUE(tdb.storage_bucket_exists(ADDR_A));
}

TYPED_TEST(PartitionedDbTest, delete_account_drops_both_stems)
{
    TrieDb tdb = this->make_tdb();
    Account const acct{.balance = 1, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{header_slot, {bytes32_t{}, value1}},
                       {zone_slot, {bytes32_t{}, value2}}}}},
             {ADDR_B, StateDelta{.account = {std::nullopt, acct}}}}),
        Code{},
        BlockHeader{.number = 0});
    EXPECT_TRUE(tdb.storage_bucket_exists(ADDR_A));

    // delete A (with a storage bucket) and B (without); storage deltas on a
    // deleted account are ignored
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, std::nullopt},
                  .storage = {{zone_slot, {value2, value1}}}}},
             {ADDR_B, StateDelta{.account = {acct, std::nullopt}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_account(ADDR_A), std::nullopt);
    EXPECT_EQ(tdb.read_account(ADDR_B), std::nullopt);
    // The DbCache keeps slots of a deleted account under its old incarnation
    // (as it does for the slot layout); execution never reads them, since it
    // reads the account first.
    if constexpr (!TypeParam::cached) {
        EXPECT_EQ(
            tdb.read_storage(ADDR_A, acct.incarnation, header_slot),
            bytes32_t{});
        EXPECT_EQ(
            tdb.read_storage(ADDR_A, acct.incarnation, zone_slot), bytes32_t{});
    }
    EXPECT_FALSE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, zone_slot)));
    EXPECT_FALSE(tdb.storage_bucket_exists(ADDR_A));
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);

    // a touched but never created account writes nothing
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_C, StateDelta{.account = {std::nullopt, std::nullopt}}}}),
        Code{},
        BlockHeader{.number = 2});
    EXPECT_EQ(tdb.read_account(ADDR_C), std::nullopt);
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(PartitionedDbTest, recreate_account_replaces_storage)
{
    TrieDb tdb = this->make_tdb();
    Account const old{
        .balance = 1, .nonce = 1, .incarnation = Incarnation{0, 1}};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, old},
                  .storage =
                      {{header_slot, {bytes32_t{}, value1}},
                       {zone_slot, {bytes32_t{}, value2}},
                       {hashed_slot, {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    // recreated in block 1 with one new zone slot: old slots vanish, the
    // header slot included
    Account const fresh{
        .balance = 2, .nonce = 1, .incarnation = Incarnation{1, 0}};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {old, fresh},
                  .storage =
                      {{zone_slot_same_group, {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(tdb.read_account(ADDR_A), fresh);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, fresh.incarnation, header_slot), bytes32_t{});
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, fresh.incarnation, zone_slot), bytes32_t{});
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, fresh.incarnation, hashed_slot), bytes32_t{});
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, fresh.incarnation, zone_slot_same_group),
        value1);
    // zone_slot shares its page leaf with the rewritten zone_slot_same_group;
    // the hashed slot's page is gone
    EXPECT_TRUE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, zone_slot)));
    EXPECT_FALSE(this->has_leaf(tdb, storage_key_nibbles(ADDR_A, hashed_slot)));
    EXPECT_TRUE(tdb.storage_bucket_exists(ADDR_A));

    // recreated again with no storage writes: the bucket goes away
    Account const again{
        .balance = 3, .nonce = 1, .incarnation = Incarnation{2, 0}};
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {fresh, again}}}}),
        Code{},
        BlockHeader{.number = 2});
    EXPECT_EQ(tdb.read_account(ADDR_A), again);
    EXPECT_FALSE(tdb.storage_bucket_exists(ADDR_A));
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, again.incarnation, zone_slot_same_group),
        bytes32_t{});
}

TYPED_TEST(PartitionedDbTest, root_depends_on_state_not_history)
{
    // Two dbs reaching the same state by different histories agree on the
    // root; a one-slot difference changes it.
    mpt::Db other_db = TypeParam::make_db();
    TrieDb a{this->db};
    TrieDb b{other_db};
    Account const acct{.balance = 9, .nonce = 2};

    commit_sequential(
        a,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{header_slot, {bytes32_t{}, value1}},
                       {zone_slot, {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    commit_sequential(
        b,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{header_slot, {bytes32_t{}, value2}},
                       {zone_slot, {bytes32_t{}, value2}},
                       {hashed_slot, {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{.number = 0});
    EXPECT_NE(a.state_root(), b.state_root());
    commit_sequential(
        b,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, acct},
                  .storage =
                      {{header_slot, {value2, value1}},
                       {hashed_slot, {value1, bytes32_t{}}}}}}}),
        Code{},
        BlockHeader{.number = 1});
    EXPECT_EQ(a.state_root(), b.state_root());
}
