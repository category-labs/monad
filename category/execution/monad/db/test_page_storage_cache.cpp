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
#include <category/execution/ethereum/db/page_storage_cache.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/monad/db/monad_page_storage_cache.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

namespace
{
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto value1 =
        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
    constexpr size_t MONAD_SLOT_BITS = 6;
    constexpr uint8_t MONAD_SLOT_MASK = 0x3F;

    using MonadCache = MonadPageStorageCache<MONAD_SLOT_BITS, MONAD_SLOT_MASK>;
}

// MonadPageStorageCache reads full pages from DB and caches them.
// Keys that share a page (same upper 250 bits) are all populated on first miss.
TEST(PageStorageCache, monad_page_read_and_cache)
{
    constexpr auto slot_key_0 = bytes32_t{0x00};
    constexpr auto slot_key_1 = bytes32_t{0x01};
    constexpr auto slot_val_0 =
        0x000000000000000000000000000000000000000000000000000000000000aaaa_bytes32;
    constexpr auto slot_val_1 =
        0x000000000000000000000000000000000000000000000000000000000000bbbb_bytes32;
    constexpr auto slot_key_far = bytes32_t{0x40};
    constexpr auto slot_val_far =
        0x000000000000000000000000000000000000000000000000000000000000cccc_bytes32;

    Account const acct{.nonce = 1};
    InMemoryMachine machine;
    mpt::Db mpt_db{machine};
    TrieDb tdb{mpt_db};

    {
        MonadCache commit_cache{tdb};
        CommitBuilder builder(0);
        builder.add_state_deltas(
            StateDeltas{
                {ADDR_A,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage =
                         {{slot_key_0, {bytes32_t{}, slot_val_0}},
                          {slot_key_1, {bytes32_t{}, slot_val_1}},
                          {slot_key_far, {bytes32_t{}, slot_val_far}}}}}},
            commit_cache);
        auto root = mpt_db.upsert(nullptr, builder.build(finalized_nibbles), 0);
        tdb.reset_root(std::move(root), 0);
    }

    MonadCache cache{tdb};

    // First read — cache miss, fetches and decodes the full page.
    EXPECT_EQ(
        cache.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_0), slot_val_0);
    EXPECT_EQ(cache.pages().size(), 1);

    // Second read — cache hit, slot 1 was populated when the page was decoded.
    auto const hit_result =
        cache.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_1);
    EXPECT_EQ(cache.pages().size(), 1);
    EXPECT_EQ(hit_result, slot_val_1);

    // Key 0x40 maps to a different page — cache miss.
    EXPECT_EQ(
        cache.read_storage(ADDR_A, Incarnation{0, 0}, slot_key_far),
        slot_val_far);
    EXPECT_EQ(cache.pages().size(), 2);

    // Verify the cached page structure.
    bytes32_t const page_key = compute_page_key<MONAD_SLOT_BITS>(slot_key_0);
    MonadCache::PageKey pk{ADDR_A, Incarnation{0, 0}, page_key};
    MonadCache::PageMap::const_accessor acc;
    ASSERT_TRUE(cache.pages().find(acc, pk));
    EXPECT_EQ(acc->second[0], slot_val_0);
    EXPECT_EQ(acc->second[1], slot_val_1);
}

// Missing key returns zero from a cached page.
TEST(PageStorageCache, monad_cache_miss_returns_zero)
{
    Account const acct{.nonce = 1};
    InMemoryMachine machine;
    mpt::Db mpt_db{machine};
    TrieDb tdb{mpt_db};

    {
        MonadCache commit_cache{tdb};
        CommitBuilder builder(0);
        builder.add_state_deltas(
            StateDeltas{
                {ADDR_A,
                 StateDelta{
                     .account = {std::nullopt, acct},
                     .storage = {{key1, {bytes32_t{}, value1}}}}}},
            commit_cache);
        auto root = mpt_db.upsert(nullptr, builder.build(finalized_nibbles), 0);
        tdb.reset_root(std::move(root), 0);
    }

    MonadCache cache{tdb};

    EXPECT_EQ(cache.read_storage(ADDR_A, Incarnation{0, 0}, key1), value1);

    // Key with no data in the trie — empty page, returns zero.
    EXPECT_EQ(
        cache.read_storage(ADDR_A, Incarnation{0, 0}, bytes32_t{}),
        bytes32_t{});
}

// NoopStorageCache with per-slot encoding (the ethereum path).
TEST(PageStorageCache, block_state_with_cache)
{
    Account const acct{.nonce = 1};
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    NoopStorageCache cache{tdb};
    BlockState block_state{tdb, cache, vm};

    auto const account = block_state.read_account(ADDR_A);
    ASSERT_TRUE(account.has_value());
    EXPECT_EQ(account->nonce, 1);

    auto const storage =
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1);
    EXPECT_EQ(storage, value1);
}
