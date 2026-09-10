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
#include <category/core/keccak.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/stamp_log.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstring>
#include <optional>
#include <random>
#include <vector>

using namespace monad;

namespace
{
    Incarnation const INC{0, 0};

    Address addr_of(uint64_t const i)
    {
        Address a{};
        std::memcpy(a.bytes + 12, &i, sizeof(i));
        return a;
    }

    bytes32_t key_of(uint64_t const i)
    {
        bytes32_t k{};
        std::memcpy(k.bytes + 24, &i, sizeof(i));
        return k;
    }

    bytes32_t const VALUE = key_of(0xabcd);

    // An account whose record changes in the block (pre -> post).
    void add_account_change(
        StateDeltas &deltas, Address const &addr, uint64_t const prev_stamp,
        std::optional<Account> const &pre, std::optional<Account> const &post)
    {
        StateDeltas::accessor it{};
        deltas.emplace(
            it,
            addr,
            StateDelta{
                .account = {pre, post},
                .storage = {},
                .account_stamp = prev_stamp});
    }

    // An account only read by the block (pre == post).
    void add_account(
        StateDeltas &deltas, Address const &addr, uint64_t const prev_stamp,
        std::optional<Account> const &pre = Account{.nonce = 1})
    {
        add_account_change(deltas, addr, prev_stamp, pre, pre);
    }

    void add_slot(
        StateDeltas &deltas, Address const &addr, bytes32_t const &key,
        bytes32_t const &pre, bytes32_t const &post, uint64_t const prev_stamp)
    {
        StateDeltas::accessor it{};
        ASSERT_TRUE(deltas.find(it, addr));
        it->second.storage.emplace(key, std::make_pair(pre, post));
        it->second.storage_stamps.try_emplace(key, prev_stamp);
    }

    struct Built
    {
        ProposalPostState post;
        StampBlockStats stats;
    };

    Built build(
        uint64_t const block, StateDeltas const &deltas,
        BlockStampCandidates const &candidates)
    {
        StampContext const ctx{.candidates = &candidates};
        CommitBuilder builder(block, &ctx);
        builder.add_state_deltas(deltas);
        return {builder.take_proposal_post_state(), builder.stamp_stats()};
    }

    bool addr_less(Address const &a, Address const &b)
    {
        return std::memcmp(a.bytes, b.bytes, sizeof(a.bytes)) < 0;
    }
}

TEST(StampRules, cached_stale_and_floor)
{
    uint64_t const n = 5000;
    EXPECT_FALSE(cache_stamp_cached(0, n));
    EXPECT_TRUE(cache_stamp_cached(n - CACHE_WINDOW_BLOCKS, n));
    EXPECT_FALSE(cache_stamp_cached(n - CACHE_WINDOW_BLOCKS - 1, n));
    EXPECT_TRUE(cache_stamp_cached(n - 1, n));
    EXPECT_FALSE(cache_stamp_stale(n - CACHE_REFRESH_PERIOD_BLOCKS, n));
    EXPECT_TRUE(cache_stamp_stale(n - CACHE_REFRESH_PERIOD_BLOCKS - 1, n));
    // young chain: nothing underflows
    EXPECT_TRUE(cache_stamp_cached(1, 10));
    EXPECT_FALSE(cache_stamp_stale(1, 10));
    EXPECT_EQ(cache_evict_floor(10), 0);
    // every stamp that can still price cached at finalized + 1 is protected
    // (the floor itself is one block of extra protection)
    uint64_t const f = 9000;
    EXPECT_TRUE(cache_stamp_cached(cache_evict_floor(f) + 1, f + 1));
    EXPECT_FALSE(cache_stamp_cached(cache_evict_floor(f), f + 1));
}

TEST(StampLogCodec, record_round_trip_and_page_layout)
{
    std::vector<Address> accounts{addr_of(1), addr_of(2)};
    std::vector<StorageKey> pages{
        StorageKey{addr_of(3), Incarnation{7, 9}, key_of(4)}};
    auto const record = encode_stamp_log_record(21001234, accounts, pages);
    EXPECT_EQ(record.size(), 16 + 20 * 2 + 60);
    auto const header = decode_stamp_log_header(record);
    ASSERT_TRUE(header.has_value());
    EXPECT_EQ(header->block, 21001234);
    EXPECT_EQ(header->n_accounts, 2);
    EXPECT_EQ(header->n_pages, 1);
    EXPECT_EQ(header->record_bytes(), record.size());
    auto const decoded = decode_stamp_log_record(record);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded->accounts, accounts);
    EXPECT_TRUE(decoded->storage[0] == pages[0]);
    // truncated input is rejected
    EXPECT_FALSE(decode_stamp_log_record(byte_string_view{record}.substr(0, 40))
                     .has_value());

    // split into pages and reassembled with trailing stale bytes ignored
    std::vector<Address> many;
    for (uint64_t i = 0; i < 300; ++i) {
        many.push_back(addr_of(i * 7919 + 1)); // includes zero-heavy words
    }
    auto const big = encode_stamp_log_record(5, many, {});
    ASSERT_GT(big.size(), STAMP_LOG_PAGE_BYTES);
    ASSERT_EQ(stamp_log_pages(big.size()), 2);
    byte_string reassembled;
    stamp_log_append_page(reassembled, stamp_log_page(big, 0));
    stamp_log_append_page(reassembled, stamp_log_page(big, 1));
    ASSERT_GE(reassembled.size(), big.size());
    EXPECT_EQ(byte_string_view{reassembled}.substr(0, big.size()), big);
    auto const decoded_big = decode_stamp_log_record(reassembled);
    ASSERT_TRUE(decoded_big.has_value());
    EXPECT_EQ(decoded_big->accounts, many);

    // ring layout: slot b mod 1000, 128 pages per slot, key = page index
    EXPECT_EQ(
        stamp_log_page_key(21001234, 3),
        store_be_as<bytes32_t>(uint256_t{234 * STAMP_LOG_PAGES_PER_SLOT + 3}));
    EXPECT_EQ(stamp_log_page_key(1000, 0), stamp_log_page_key(2000, 0));
}

TEST(StampSelection, classes_caps_order_and_dead_items)
{
    uint64_t const n = 20000;
    StateDeltas deltas;
    BlockStampCandidates candidates(1);
    auto &tx = candidates[0];

    // 6000 cold live accounts read: class 1, more than the cap
    for (uint64_t i = 1; i <= 6000; ++i) {
        add_account(deltas, addr_of(i), 0);
        tx.accounts.push_back(addr_of(i));
    }
    // a cached, fresh read: no candidate
    add_account(deltas, addr_of(7001), n - 10);
    tx.accounts.push_back(addr_of(7001));
    // a cached, stale read: class 3
    add_account(deltas, addr_of(7002), n - 600);
    tx.accounts.push_back(addr_of(7002));
    // a value-changing write to a cached account: class 2
    add_account_change(
        deltas,
        addr_of(7003),
        n - 10,
        Account{.nonce = 1},
        Account{.nonce = 2});
    // a cold live account read then deleted in the block: not a candidate
    add_account_change(
        deltas, addr_of(7004), 0, Account{.nonce = 1}, std::nullopt);
    tx.accounts.push_back(addr_of(7004));
    // a read of a nonexistent account: never a candidate
    add_account(deltas, addr_of(7005), 0, std::nullopt);
    tx.accounts.push_back(addr_of(7005));
    // a created account: no candidate (not live in pre-state)
    add_account_change(
        deltas, addr_of(7006), 0, std::nullopt, Account{.nonce = 1});

    // storage: cold read of a live slot (class 1), stale cached read (class
    // 3), cached write (class 2), zeroed slot (dead), cold write to a live
    // slot (class 1 through the journal)
    Address const c = addr_of(9000);
    add_account(deltas, c, n - 10);
    add_slot(deltas, c, key_of(1), VALUE, VALUE, 0);
    tx.storage.emplace_back(c, key_of(1));
    add_slot(deltas, c, key_of(2), VALUE, VALUE, n - 600);
    tx.storage.emplace_back(c, key_of(2));
    add_slot(deltas, c, key_of(3), VALUE, key_of(99), n - 10);
    tx.storage.emplace_back(c, key_of(3));
    add_slot(deltas, c, key_of(4), VALUE, bytes32_t{}, 0);
    tx.storage.emplace_back(c, key_of(4));
    add_slot(deltas, c, key_of(5), VALUE, key_of(98), 0);
    tx.storage.emplace_back(c, key_of(5));
    add_slot(deltas, c, key_of(6), bytes32_t{}, VALUE, 0); // creation

    auto const [post, stats] = build(n, deltas, candidates);

    EXPECT_EQ(stats.account_candidates[0], 6000);
    EXPECT_EQ(stats.account_candidates[1], 1);
    EXPECT_EQ(stats.account_candidates[2], 1);
    EXPECT_TRUE(stats.account_cap_hit);
    EXPECT_EQ(stats.selected_accounts, MAX_ACCOUNT_STAMPS_PER_BLOCK);
    ASSERT_EQ(post.account_stamps.size(), MAX_ACCOUNT_STAMPS_PER_BLOCK);
    // selection order: class 1 first, byte-lexicographic within the class
    std::vector<Address> expected;
    for (uint64_t i = 1; i <= 6000; ++i) {
        expected.push_back(addr_of(i));
    }
    std::sort(expected.begin(), expected.end(), addr_less);
    expected.resize(MAX_ACCOUNT_STAMPS_PER_BLOCK);
    EXPECT_EQ(post.account_stamps, expected);
    EXPECT_EQ(stats.accounts_written, 3); // 7003, 7004, 7006

    EXPECT_EQ(stats.page_candidates[0], 2); // slots 1 and 5
    EXPECT_EQ(stats.page_candidates[1], 1); // slot 3
    EXPECT_EQ(stats.page_candidates[2], 1); // slot 2
    EXPECT_FALSE(stats.page_cap_hit);
    ASSERT_EQ(post.storage_stamps.size(), 4);
    std::vector<StorageKey> const expected_pages{
        StorageKey{c, INC, key_of(1)},
        StorageKey{c, INC, key_of(5)},
        StorageKey{c, INC, key_of(3)},
        StorageKey{c, INC, key_of(2)}};
    for (size_t i = 0; i < 4; ++i) {
        EXPECT_TRUE(post.storage_stamps[i] == expected_pages[i]) << i;
    }
    EXPECT_EQ(stats.selected_slots, 4);
    EXPECT_EQ(stats.pages_written, 4); // slots 3, 4, 5, 6
    EXPECT_EQ(stats.slots_written, 3); // slot 4 is now empty
    EXPECT_EQ(
        stats.record_bytes, 16 + 20 * MAX_ACCOUNT_STAMPS_PER_BLOCK + 60 * 4);
    EXPECT_EQ(stats.log_pages, stamp_log_pages(stats.record_bytes));
}

TEST(StampSelection, slot_weighted_page_cap_and_determinism)
{
    uint64_t const n = 20000;
    StateDeltas deltas;
    BlockStampCandidates candidates(2);
    Address const c = addr_of(1);
    add_account(deltas, c, 0);
    // 5001 cold live slots across two transactions, in scrambled order
    std::vector<uint64_t> order(5001);
    for (uint64_t i = 0; i < order.size(); ++i) {
        order[i] = i + 1;
    }
    std::shuffle(order.begin(), order.end(), std::mt19937{42});
    for (size_t i = 0; i < order.size(); ++i) {
        add_slot(deltas, c, key_of(order[i]), VALUE, VALUE, 0);
        candidates[i % 2].storage.emplace_back(c, key_of(order[i]));
    }
    auto const [post, stats] = build(n, deltas, candidates);
    EXPECT_TRUE(stats.page_cap_hit);
    EXPECT_EQ(stats.selected_slots, MAX_STORAGE_SLOT_STAMPS_PER_BLOCK);
    ASSERT_EQ(post.storage_stamps.size(), MAX_STORAGE_SLOT_STAMPS_PER_BLOCK);
    // the byte-lexicographically largest key is the one dropped
    uint64_t largest = 1;
    for (uint64_t i = 2; i <= 5001; ++i) {
        if (std::memcmp(key_of(i).bytes, key_of(largest).bytes, 32) > 0) {
            largest = i;
        }
    }
    auto const dropped = StorageKey{c, INC, key_of(largest)};
    EXPECT_TRUE(std::none_of(
        post.storage_stamps.begin(),
        post.storage_stamps.end(),
        [&](auto const &k) { return k == dropped; }));

    // same block, different journal order: byte-identical record
    BlockStampCandidates reordered(1);
    for (auto const &tx : candidates) {
        for (auto it = tx.storage.rbegin(); it != tx.storage.rend(); ++it) {
            reordered[0].storage.push_back(*it);
        }
    }
    auto const [post2, stats2] = build(n, deltas, reordered);
    EXPECT_EQ(stats2.record_hash, stats.record_hash);
    EXPECT_EQ(post2.storage_stamps.size(), post.storage_stamps.size());
}

TEST(StampLru, stamp_order_eviction_and_negative_list)
{
    LruCache<int, std::optional<int>> cache{
        /*max_size=*/3, /*stamp_mode=*/true, /*negative_max=*/2};
    cache.set_evict_floor(0);

    // negatives never displace live entries
    for (int k = 0; k < 3; ++k) {
        cache.insert(k, k);
        cache.set_stamp(k, static_cast<uint64_t>(k) + 1);
    }
    for (int k = 100; k < 110; ++k) {
        cache.insert(k, std::nullopt, /*negative=*/true);
    }
    for (int k = 0; k < 3; ++k) {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, k));
        EXPECT_EQ(cache.stamp_of(acc), static_cast<uint64_t>(k) + 1);
    }

    // floor advanced past stamp 1: key 0 has expired and is the eviction
    // victim of the next live insert (a cached victim would abort)
    cache.set_evict_floor(2);
    cache.insert(50, 50);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        EXPECT_FALSE(cache.find(acc, 0));
        ASSERT_TRUE(cache.find(acc, 50));
        EXPECT_EQ(cache.stamp_of(acc), 0); // unstamped until finalize
    }

    // deletion flips the entry to the negative list in place
    cache.insert(1, std::nullopt, /*negative=*/true);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, 1));
        EXPECT_TRUE(cache.is_negative(acc));
        EXPECT_EQ(cache.stamp_of(acc), 0);
    }
    // and creation flips it back, unstamped
    cache.insert(1, 11);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, 1));
        EXPECT_FALSE(cache.is_negative(acc));
        EXPECT_EQ(cache.stamp_of(acc), 0);
    }
}

TEST(StampDbCache, finalize_stamps_and_deletion_forgets)
{
    DbCache cache;
    Address const a = addr_of(1);
    Address const b = addr_of(2);
    ProposalPostState post;
    post.accounts[a] = Account{.nonce = 1};
    post.accounts[b] = Account{.nonce = 1};
    post.account_stamps = {a, b};
    cache.update_proposal_state(std::move(post), 10, bytes32_t{10});
    cache.on_finalize(10, bytes32_t{10});
    EXPECT_TRUE(cache.account_has_stamp(a, 10));
    EXPECT_TRUE(cache.account_has_stamp(b, 10));

    // block 11 deletes b and recreates it in block 12 through the proposal
    // chain: the overlay prices it cold at every point, exactly like the
    // physical entry after finalize
    cache.set_block_and_prefix(10, bytes32_t{10});
    ProposalPostState del;
    del.accounts[b] = std::nullopt;
    cache.update_proposal_state(std::move(del), 11, bytes32_t{11});
    cache.set_block_and_prefix(11, bytes32_t{11});
    ProposalPostState recreate;
    recreate.accounts[b] = Account{.nonce = 5};
    cache.update_proposal_state(std::move(recreate), 12, bytes32_t{12});
    cache.set_block_and_prefix(12, bytes32_t{12});
    std::optional<Account> result;
    uint64_t stamp = 99;
    EXPECT_EQ(cache.try_read_account(b, result, &stamp), CacheReadStatus::Hit);
    EXPECT_EQ(stamp, 0);
    EXPECT_EQ(cache.try_read_account(a, result, &stamp), CacheReadStatus::Hit);
    EXPECT_EQ(stamp, 10);
    cache.on_finalize(11, bytes32_t{11});
    EXPECT_FALSE(cache.account_has_stamp(b, 10));
    cache.on_finalize(12, bytes32_t{12});
    EXPECT_TRUE(cache.account_has_stamp(b, 0));
    EXPECT_TRUE(cache.account_has_stamp(a, 10));
}

namespace
{
    // Commit one block through TrieDb with stamp selection, the way the
    // runloops do (deltas built by hand, stamps memoized from stamped reads).
    void commit_block(
        TrieDb &tdb, uint64_t const n, StateDeltas const &deltas,
        BlockStampCandidates const &candidates)
    {
        StampContext const ctx{.candidates = &candidates};
        CommitBuilder builder(n, &ctx);
        builder.add_state_deltas(deltas)
            .add_code({})
            .add_receipts({})
            .add_transactions({}, {})
            .add_call_frames({})
            .add_ommers({});
        BlockHeader header;
        header.number = n;
        bytes32_t const block_id{n};
        tdb.commit(block_id, builder, header, deltas, [&](BlockHeader &h) {
            h.receipts_root = tdb.receipts_root();
            h.state_root = tdb.state_root();
            h.transactions_root = tdb.transactions_root();
        });
        tdb.finalize(n, block_id);
    }
}

TEST(StampBootstrap, restart_reproduces_stamps_from_the_log)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db, /*enable_multiblock_cache=*/true};

    // block 1 creates the accounts and slots (no stamps: not live before)
    {
        StateDeltas deltas;
        for (uint64_t i = 1; i <= 30; ++i) {
            add_account_change(
                deltas, addr_of(i), 0, std::nullopt, Account{.nonce = 1});
        }
        for (uint64_t i = 1; i <= 8; ++i) {
            add_slot(deltas, addr_of(1), key_of(i), bytes32_t{}, VALUE, 0);
        }
        commit_block(tdb, 1, deltas, {});
    }
    // blocks 2..4: cold reads stamp accounts 1..10 at block 2, 11..20 at 3,
    // and slots 1..8 plus a re-read of account 1 (cached, fresh: no stamp)
    // at 4; account 21 is deleted at 4 after being stamped at 3
    auto read_block = [&](uint64_t const n,
                          std::vector<uint64_t> const &accounts,
                          std::vector<uint64_t> const &slots,
                          std::optional<uint64_t> const deleted) {
        tdb.set_block_and_prefix(n - 1);
        StateDeltas deltas;
        BlockStampCandidates candidates(1);
        for (uint64_t const i : accounts) {
            uint64_t stamp = 0;
            auto const acct = tdb.read_account_stamped(addr_of(i), stamp);
            ASSERT_TRUE(acct.has_value());
            add_account(deltas, addr_of(i), stamp, acct);
            candidates[0].accounts.push_back(addr_of(i));
        }
        if (!slots.empty()) {
            uint64_t stamp = 0;
            auto const acct = tdb.read_account_stamped(addr_of(1), stamp);
            if (!deltas.count(addr_of(1))) {
                add_account(deltas, addr_of(1), stamp, acct);
            }
            for (uint64_t const i : slots) {
                uint64_t sstamp = 0;
                auto const v = tdb.read_storage_stamped(
                    addr_of(1), INC, key_of(i), sstamp);
                ASSERT_EQ(v, VALUE);
                add_slot(deltas, addr_of(1), key_of(i), v, v, sstamp);
                candidates[0].storage.emplace_back(addr_of(1), key_of(i));
            }
        }
        if (deleted.has_value()) {
            uint64_t stamp = 0;
            auto const acct =
                tdb.read_account_stamped(addr_of(*deleted), stamp);
            add_account_change(
                deltas, addr_of(*deleted), stamp, acct, std::nullopt);
        }
        commit_block(tdb, n, deltas, candidates);
    };
    read_block(2, {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {}, std::nullopt);
    read_block(
        3, {11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21}, {}, std::nullopt);
    read_block(4, {1}, {1, 2, 3, 4, 5, 6, 7, 8}, 21);

    tdb.set_block_and_prefix(4);
    uint64_t stamp = 0;
    tdb.read_account_stamped(addr_of(1), stamp);
    EXPECT_EQ(stamp, 2); // fresh cached read did not re-stamp
    tdb.read_account_stamped(addr_of(15), stamp);
    EXPECT_EQ(stamp, 3);
    tdb.read_account_stamped(addr_of(25), stamp);
    EXPECT_EQ(stamp, 0);
    tdb.read_storage_stamped(addr_of(1), INC, key_of(3), stamp);
    EXPECT_EQ(stamp, 4);
    EXPECT_FALSE(tdb.read_account_stamped(addr_of(21), stamp).has_value());

    // a fresh node over the same state rebuilds every stamp from the ring
    // (an in-memory db has no persisted root, so hand it over explicitly)
    TrieDb restarted{db, /*enable_multiblock_cache=*/true};
    restarted.reset_root(tdb.get_root(), 4);
    auto const rebuilt = restarted.rebuild_stamp_cache();
    EXPECT_EQ(rebuilt.records, 4); // blocks 1..4 each wrote a record
    EXPECT_EQ(rebuilt.accounts, 20); // 21 died after its stamp
    EXPECT_EQ(rebuilt.pages, 8);
    EXPECT_EQ(rebuilt.slots, 8);
    for (uint64_t i = 1; i <= 30; ++i) {
        uint64_t live = 0;
        uint64_t again = 0;
        tdb.read_account_stamped(addr_of(i), live);
        restarted.read_account_stamped(addr_of(i), again);
        EXPECT_EQ(live, again) << "account " << i;
    }
    for (uint64_t i = 1; i <= 8; ++i) {
        uint64_t live = 0;
        uint64_t again = 0;
        tdb.read_storage_stamped(addr_of(1), INC, key_of(i), live);
        restarted.read_storage_stamped(addr_of(1), INC, key_of(i), again);
        EXPECT_EQ(live, again) << "slot " << i;
    }
    // the log itself is invisible to reads
    EXPECT_EQ(
        restarted.read_storage(STAMP_LOG_ADDRESS, INC, key_of(0)), bytes32_t{});
}
