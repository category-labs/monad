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

#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/monad/db/monad_commit_builder.hpp>
#include <category/execution/monad/db/page_storage_broker.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstring>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

TEST(MonadDb, key_grouping)
{
    // Keys 0x00..0x7F should all map to the same page (page_key = 0)
    bytes32_t const page_key_0 = compute_page_key(bytes32_t{0});

    for (uint8_t i = 0; i < 128; ++i) {
        bytes32_t const slot_key = bytes32_t{i};
        EXPECT_EQ(compute_page_key(slot_key), page_key_0)
            << "slot " << static_cast<int>(i)
            << " should map to same page as slot 0";
        EXPECT_EQ(compute_slot_offset(slot_key), i)
            << "slot " << static_cast<int>(i)
            << " should have offset equal to its low bits";
    }

    // Key 0x80 should map to a different page
    bytes32_t const slot_128 = bytes32_t{0x80};
    EXPECT_NE(compute_page_key(slot_128), page_key_0);
    EXPECT_EQ(compute_slot_offset(slot_128), 0);

    // Keys 0x80..0xFF should share a second page
    bytes32_t const page_key_1 = compute_page_key(bytes32_t{0x80});
    for (uint16_t i = 0x80; i < 0x100; ++i) {
        bytes32_t const slot_key = bytes32_t{static_cast<uint8_t>(i)};
        EXPECT_EQ(compute_page_key(slot_key), page_key_1);
        EXPECT_EQ(
            compute_slot_offset(slot_key),
            static_cast<uint8_t>(i & storage_page_t::SLOT_OFFSET_MASK));
    }

    // Round-trip for all keys 0..0xFF
    for (uint16_t i = 0; i < 256; ++i) {
        bytes32_t const slot_key = bytes32_t{static_cast<uint8_t>(i)};
        bytes32_t const pk = compute_page_key(slot_key);
        uint8_t const off = compute_slot_offset(slot_key);
        EXPECT_EQ(compute_slot_key(pk, off), slot_key);
    }
}

// Slots on the same page are merged into a single page on commit.
// Block 0 writes slots 0 and 1. Block 1 updates slot 0 only.
// After block 1 commit, both the updated slot 0 and the untouched slot 1
// must be present in the same page.
TEST(MonadDb, page_write_merges_slots)
{
    constexpr auto slot_key_0 = bytes32_t{0x00};
    constexpr auto slot_key_1 = bytes32_t{0x01};
    constexpr auto val_0 =
        0x000000000000000000000000000000000000000000000000000000000000aaaa_bytes32;
    constexpr auto val_1 =
        0x000000000000000000000000000000000000000000000000000000000000bbbb_bytes32;
    constexpr auto val_0_updated =
        0x000000000000000000000000000000000000000000000000000000000000dddd_bytes32;

    Account const acct{.nonce = 1};
    InMemoryMachine machine;
    mpt::Db mpt_db{machine};
    TrieDb tdb{mpt_db};

    // Block 0: seed two slots on the same page.
    {
        PageStorageBroker broker{tdb};
        MonadCommitBuilder builder(0, broker);
        builder.add_state_deltas(StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {
                     {slot_key_0, {bytes32_t{}, val_0}},
                     {slot_key_1, {bytes32_t{}, val_1}}}}}});
        auto root = mpt_db.upsert(nullptr, builder.build(finalized_nibbles), 0);
        tdb.reset_root(std::move(root), 0);
    }

    // Block 1: update slot 0, leave slot 1 untouched.
    // The broker reads the existing page (both slots), the commit builder
    // merges the delta on top, so the resulting page keeps both values.
    {
        PageStorageBroker broker{tdb};

        // Populate broker by reading through it.
        ASSERT_EQ(
            broker.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_0), val_0);
        ASSERT_EQ(
            broker.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_1), val_1);

        MonadCommitBuilder builder(1, broker);
        builder.add_state_deltas(StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{slot_key_0, {val_0, val_0_updated}}}}}});
        auto root =
            mpt_db.upsert(tdb.get_root(), builder.build(finalized_nibbles), 1);
        tdb.reset_root(std::move(root), 1);
    }

    // Verify: fresh broker reads back both values from the committed page.
    PageStorageBroker broker{tdb};
    EXPECT_EQ(
        broker.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_0),
        val_0_updated);
    EXPECT_EQ(
        broker.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_1), val_1);
}

TEST(MonadDb, page_commit_deterministic)
{
    storage_page_t page{};
    auto const c1 = page_commit(page);
    auto const c2 = page_commit(page);
    EXPECT_EQ(c1, c2);
    EXPECT_NE(c1, bytes32_t{});
}

TEST(MonadDb, page_commit_differs_for_different_pages)
{
    storage_page_t page_a{};
    storage_page_t page_b{};
    page_b[0] = bytes32_t{0x01};

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sensitive_to_slot_position)
{
    storage_page_t page_a{};
    page_a[0] = bytes32_t{0x01};

    storage_page_t page_b{};
    page_b[1] = bytes32_t{0x01};

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sensitive_to_distant_slots)
{
    storage_page_t page_a{};
    page_a[0] = bytes32_t{0x01};

    storage_page_t page_b{};
    page_b[127] = bytes32_t{0x01};

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sparse_nonzero)
{
    storage_page_t page{};
    std::memset(&page[0], 0x11, sizeof(bytes32_t));
    std::memset(&page[2], 0x22, sizeof(bytes32_t));
    std::memset(&page[4], 0x33, sizeof(bytes32_t));

    storage_page_t zero_page{};
    EXPECT_NE(page_commit(page), page_commit(zero_page));
    EXPECT_EQ(page_commit(page), page_commit(page));
}

TEST(MonadDb, page_commit_uniform_fill_differs)
{
    storage_page_t page_a{};
    std::memset(&page_a, 0x11, sizeof(page_a));

    storage_page_t page_b{};
    std::memset(&page_b, 0x22, sizeof(page_b));

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_cross_check_with_reference)
{
    constexpr auto ZERO_PAGE_COMMIT =
        0x89c59adeeea5e67e3cbccae4e6098c6afbdad96c396a7b86804f949345fded3d_bytes32;
    constexpr auto SLOT0_ONE_COMMIT =
        0x1abb7bae420b1a04f507458dbc01829d1f906351147452883e4d1c8133f75474_bytes32;
    constexpr auto SLOT127_ONE_COMMIT =
        0x935ebada7ce100f6d5eb7dc709909747f302e900be73f0a8c13146de3f480e14_bytes32;
    constexpr auto FULL_PAGE_COMMIT =
        0x36b8719c5b7ba4ad58227e4c768e9d45384ab92dddab881a7cbe81a46a7b1d2a_bytes32;

    storage_page_t zero_page{};
    EXPECT_EQ(page_commit(zero_page), ZERO_PAGE_COMMIT);

    storage_page_t page_slot0{};
    page_slot0[0] = bytes32_t{0x01};
    EXPECT_EQ(page_commit(page_slot0), SLOT0_ONE_COMMIT);

    storage_page_t page_slot127{};
    page_slot127[127] = bytes32_t{0x01};
    EXPECT_EQ(page_commit(page_slot127), SLOT127_ONE_COMMIT);

    storage_page_t full_page{};
    for (uint8_t i = 0; i < 128; ++i) {
        full_page[i] = bytes32_t{static_cast<uint8_t>(i + 1)};
    }
    EXPECT_EQ(page_commit(full_page), FULL_PAGE_COMMIT);
}
