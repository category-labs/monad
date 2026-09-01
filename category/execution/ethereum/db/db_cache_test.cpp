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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr auto ADDR = 0x00000000000000000000000000000000000000aa_address;
    constexpr auto OTHER_ADDR =
        0x00000000000000000000000000000000000000bb_address;
    constexpr auto KEY =
        0x00000000000000000000000000000000000000000000000000000000000000aa_bytes32;
    constexpr auto OTHER_KEY =
        0x00000000000000000000000000000000000000000000000000000000000000bb_bytes32;
    constexpr auto VALUE1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto VALUE2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;

    Incarnation const INC{0, 0};

    ProposalPostState make_post_state(
        Address const &addr, bytes32_t const &key, bytes32_t const &value)
    {
        ProposalPostState post;
        post.accounts[addr] = Account{.nonce = 1};
        post.storage[StorageKey{addr, INC, key}] = storage_page_t{value};
        return post;
    }
}

TEST(DbCacheTest, unknown_proposal_cursor_is_miss_truncated)
{
    DbCache cache;
    cache.set_block_and_prefix(3, bytes32_t{9});

    // proposal id has nothing.
    storage_page_t page;
    EXPECT_EQ(
        cache.try_read_storage_page(ADDR, INC, KEY, page),
        CacheReadStatus::MissTruncated);
}

TEST(DbCacheTest, write_beyond_depth_limit_is_miss_truncated)
{

    DbCache cache;
    cache.update_proposal_state(
        make_post_state(ADDR, KEY, VALUE2), 1, bytes32_t{1});

    // proposals 2..6 are padding that only touch OTHER_ADDR/OTHER_KEY. the
    // walk in Proposals::try_read checks at most DEPTH_LIMIT = 5 entries, so
    // from the tip it visits 6, 5, 4, 3, 2 and gives up before reaching
    // proposal 1's write.
    for (uint64_t n = 2; n <= 6; ++n) {
        cache.update_proposal_state(
            make_post_state(OTHER_ADDR, OTHER_KEY, VALUE1), n, bytes32_t{n});
    }

    // point reads at the branch tip.
    cache.set_block_and_prefix(6, bytes32_t{6});

    // truncates before reaching proposal 1
    storage_page_t page;
    EXPECT_EQ(
        cache.try_read_storage_page(ADDR, INC, KEY, page),
        CacheReadStatus::MissTruncated);

    // same for the account map.
    std::optional<Account> acct;
    EXPECT_EQ(
        cache.try_read_account(ADDR, acct), CacheReadStatus::MissTruncated);
}

TEST(DbCacheTest, proposal_write_shadows_readthrough_entry)
{
    DbCache cache;
    cache.update_proposal_state(
        make_post_state(OTHER_ADDR, OTHER_KEY, VALUE2), 1, bytes32_t{1});
    cache.set_block_and_prefix(1, bytes32_t{1});

    // populate the read-through entry. the walk from proposal 1 reaches the
    // finalized base without finding KEY, so db will fetch VALUE1 from
    // disk and cache it.
    bytes32_t slot;
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot),
        CacheReadStatus::MissResolved);
    cache.insert_storage_page(ADDR, INC, KEY, storage_page_t{VALUE1});

    // verify read through entry is populated
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(slot, VALUE1);

    // proposal 2 writes KEY = VALUE2: the LRU entry is now stale relative
    // to this branch.
    cache.update_proposal_state(
        make_post_state(ADDR, KEY, VALUE2), 2, bytes32_t{2});
    cache.set_block_and_prefix(2, bytes32_t{2});

    // The overlay walk must serve proposal 2's write
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(slot, VALUE2);
}

TEST(DbCacheTest, finalization_write_overwrites_readthrough_entry)
{
    DbCache cache;
    cache.update_proposal_state(
        make_post_state(OTHER_ADDR, OTHER_KEY, VALUE2), 1, bytes32_t{1});
    cache.set_block_and_prefix(1, bytes32_t{1});

    // populate the read-through entry. the walk from proposal 1 reaches the
    // finalized base without finding KEY, so db will fetch VALUE1 from
    // disk and cache it.
    bytes32_t slot;
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot),
        CacheReadStatus::MissResolved);
    cache.insert_storage_page(ADDR, INC, KEY, storage_page_t{VALUE1});

    // verify readthrough entry is populated
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(slot, VALUE1);

    // proposal 2 writes KEY = VALUE2; proposal 3 builds on top of it without
    // touching KEY, so its reads must come from the LRU.
    cache.update_proposal_state(
        make_post_state(ADDR, KEY, VALUE2), 2, bytes32_t{2});
    cache.update_proposal_state(
        make_post_state(OTHER_ADDR, OTHER_KEY, VALUE1), 3, bytes32_t{3});

    // readthrough VALUE1 is replaced by VALUE2.
    cache.on_finalize(1, bytes32_t{1});
    cache.on_finalize(2, bytes32_t{2});

    // clean walk from proposal 3 to finalized 2 finds no writer of KEY, so
    // the LRU answers — it must serve the finalized VALUE2, not the stale
    // read-through VALUE1.
    cache.set_block_and_prefix(3, bytes32_t{3});
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(slot, VALUE2);
}

TEST(DbCacheTest, proposal_overlay_hits_are_not_counted_against_the_lru)
{
    DbCache cache;
    cache.update_proposal_state(
        make_post_state(ADDR, KEY, VALUE1), 1, bytes32_t{1});
    cache.set_block_and_prefix(1, bytes32_t{1});

    std::optional<Account> account;
    EXPECT_EQ(cache.try_read_account(ADDR, account), CacheReadStatus::Hit);

    auto const stats = cache.stats();
    EXPECT_EQ(stats.accounts.hits, 0u);
    EXPECT_EQ(stats.accounts.misses, 0u);
}

namespace
{
    // Never written by any proposal, so reads of it fall through to the LRU.
    constexpr auto UNWRITTEN_ADDR =
        0x00000000000000000000000000000000000000cc_address;
    constexpr auto UNWRITTEN_KEY =
        0x00000000000000000000000000000000000000000000000000000000000000cc_bytes32;

    // Proposals 1 and 2 write ADDR/KEY and are finalized, promoting them into
    // the LRUs; proposal 3 is the block being read from and writes neither,
    // so a read of ADDR/KEY walks clean to the finalized base and the LRU
    // answers.
    void seed_finalized_lru(DbCache &cache)
    {
        cache.update_proposal_state(
            make_post_state(ADDR, KEY, VALUE1), 1, bytes32_t{1});
        cache.update_proposal_state(
            make_post_state(ADDR, KEY, VALUE2), 2, bytes32_t{2});
        cache.update_proposal_state(
            make_post_state(OTHER_ADDR, OTHER_KEY, VALUE1), 3, bytes32_t{3});
        cache.on_finalize(1, bytes32_t{1});
        cache.on_finalize(2, bytes32_t{2});
        cache.set_block_and_prefix(3, bytes32_t{3});
    }
}

TEST(DbCacheTest, counts_lru_account_hits_and_misses)
{
    DbCache cache;
    seed_finalized_lru(cache);

    std::optional<Account> account;
    EXPECT_EQ(cache.try_read_account(ADDR, account), CacheReadStatus::Hit);
    EXPECT_EQ(
        cache.try_read_account(UNWRITTEN_ADDR, account),
        CacheReadStatus::MissResolved);

    auto const stats = cache.stats();
    EXPECT_EQ(stats.accounts.hits, 1u);
    EXPECT_EQ(stats.accounts.misses, 1u);
}

// Both views must be available at once from the same cache.
TEST(DbCacheTest, block_stats_count_only_what_happened_since_the_snapshot)
{
    DbCache cache;
    seed_finalized_lru(cache);

    std::optional<Account> account;
    ASSERT_EQ(cache.try_read_account(ADDR, account), CacheReadStatus::Hit);

    cache.begin_block_stats();
    ASSERT_EQ(cache.try_read_account(ADDR, account), CacheReadStatus::Hit);

    EXPECT_EQ(cache.stats().accounts.hits, 2u);
    EXPECT_EQ(cache.block_stats().accounts.hits, 1u);
}

TEST(DbCacheTest, consecutive_blocks_do_not_accumulate_in_block_stats)
{
    DbCache cache;
    seed_finalized_lru(cache);

    std::optional<Account> account;
    bytes32_t slot;

    cache.begin_block_stats();
    ASSERT_EQ(cache.try_read_account(ADDR, account), CacheReadStatus::Hit);
    ASSERT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(cache.block_stats().accounts.hits, 1u);
    EXPECT_EQ(cache.block_stats().storage.hits, 1u);

    // A second block with no reads at all must report zero, not the first
    // block's totals.
    cache.begin_block_stats();
    EXPECT_EQ(cache.block_stats().accounts.hits, 0u);
    EXPECT_EQ(cache.block_stats().storage.hits, 0u);
    EXPECT_EQ(cache.stats().accounts.hits, 1u);
    EXPECT_EQ(cache.stats().storage.hits, 1u);
}

TEST(DbCacheTest, counts_lru_storage_hits_and_misses)
{
    DbCache cache;
    seed_finalized_lru(cache);

    bytes32_t slot;
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, KEY, 0, slot), CacheReadStatus::Hit);
    EXPECT_EQ(
        cache.try_read_storage(ADDR, INC, UNWRITTEN_KEY, 0, slot),
        CacheReadStatus::MissResolved);

    auto const stats = cache.stats();
    EXPECT_EQ(stats.storage.hits, 1u);
    EXPECT_EQ(stats.storage.misses, 1u);
}
