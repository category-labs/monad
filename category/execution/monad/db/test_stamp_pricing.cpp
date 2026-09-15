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
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/stamp_log.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstring>
#include <optional>
#include <random>
#include <thread>
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

    void commit_block(
        TrieDb &db, uint64_t n, StateDeltas const &deltas,
        BlockStampCandidates const &candidates)
    {
        StampContext const ctx{.candidates = &candidates, .db = &db};
        auto builder = make_commit_builder(n, db, &ctx);
        builder->add_state_deltas(deltas)
            .add_code({})
            .add_receipts({})
            .add_transactions({}, {})
            .add_call_frames({})
            .add_ommers({});
        BlockHeader header;
        header.number = n;
        bytes32_t const id{n};
        db.commit(id, *builder, header, deltas, [&](BlockHeader &h) {
            h.receipts_root = db.receipts_root();
            h.state_root = db.state_root();
            h.transactions_root = db.transactions_root();
        });
        db.finalize(n, id);
        db.set_block_and_prefix(n);
    }

    struct RingStore
    {
        CachePageUpdates pages;

        CachePageReader reader()
        {
            return
                [this](bytes32_t const &key) -> std::optional<storage_page_t> {
                    auto it = pages.find(key);
                    return it == pages.end() ? std::nullopt
                                             : std::make_optional(it->second);
                };
        }

        void save(CacheRingWriter &writer)
        {
            for (auto &[key, page] : writer.finish()) {
                pages[key] = std::move(page);
            }
        }
    };

    CacheRingRecord record(uint64_t i, uint8_t weight = 1)
    {
        return {StorageKey{addr_of(i), INC, key_of(i)}, weight};
    }

    DbCacheSizes const SMALL_CACHE{1000, 1024 * 1024, 100};
}

TEST(CachePricing, range_and_fixed_allowance)
{
    CacheRingView const view{193, 500, 385};
    EXPECT_FALSE(cache_stamp_cached(0, view));
    EXPECT_FALSE(cache_stamp_cached(192, view));
    EXPECT_TRUE(cache_stamp_cached(193, view));
    EXPECT_TRUE(cache_stamp_cached(499, view));
    EXPECT_FALSE(cache_stamp_cached(500, view));
    EXPECT_TRUE(cache_stamp_stale(384, view));
    EXPECT_FALSE(cache_stamp_stale(385, view));
    EXPECT_EQ(cache_tx_credits(1999), 0);
    EXPECT_EQ(cache_tx_credits(21000), 10);
    EXPECT_EQ(cache_tx_credits(1000000), 256);
}

TEST(CacheRing, codecs_and_layout)
{
    for (auto const &config : {ACCOUNT_RING, STORAGE_RING}) {
        RingStore store;
        CacheRingWriter writer{config, store.reader()};
        for (uint64_t i = 1; i <= config.records_per_index; ++i) {
            EXPECT_EQ(
                writer.append(record(
                    i, config.kind == CacheRingKind::accounts ? 1 : 128)),
                i);
        }
        auto cursor = writer.cursor();
        store.save(writer);
        EXPECT_EQ(read_cache_cursor(config, store.reader()), cursor);
        auto const &page =
            store.pages.at(cache_ring_key(config, CacheRingPart::records, 1));
        auto decoded = decode_cache_chunk(config, page, 1);
        EXPECT_EQ(decoded.records.size(), config.records_per_index);
        EXPECT_EQ(encode_cache_chunk(config, decoded), page);
        EXPECT_EQ(
            cache_ring_key(config, CacheRingPart::records, 1),
            cache_ring_key(config, CacheRingPart::records, config.indices + 1));
        EXPECT_NE(
            cache_ring_key(config, CacheRingPart::records, 1),
            cache_ring_key(config, CacheRingPart::cursor));
        EXPECT_DEATH(decode_cache_chunk(config, page, 2), "Assertion");
        auto corrupt = page;
        corrupt.set(0, VALUE);
        EXPECT_DEATH(decode_cache_chunk(config, corrupt, 1), "Assertion");
    }
    EXPECT_EQ(
        cache_ring_key(ACCOUNT_RING, CacheRingPart::cursor),
        cache_ring_key(STORAGE_RING, CacheRingPart::cursor));
    for (auto const &config : {ACCOUNT_RING, STORAGE_RING}) {
        for (auto const part :
             {CacheRingPart::cursor, CacheRingPart::records}) {
            auto const page_key = cache_ring_key(config, part, 1);
            auto const slot =
                store_be_as<bytes32_t>(load_be<uint256_t>(page_key.bytes) << 7);
            EXPECT_EQ(compute_page_key(slot), page_key);
        }
    }
}

TEST(CacheRing, partial_chunk_survives_empty_blocks)
{
    RingStore store;
    for (uint64_t block = 1; block <= 200; ++block) {
        CacheRingWriter writer{ACCOUNT_RING, store.reader()};
        EXPECT_EQ(writer.append(record(block)), block);
        store.save(writer);
        CacheRingWriter empty{ACCOUNT_RING, store.reader()};
        EXPECT_TRUE(empty.finish().empty());
    }
    auto const cursor = read_cache_cursor(ACCOUNT_RING, store.reader());
    EXPECT_EQ(cursor.view.floor, 1);
    EXPECT_EQ(cursor.view.next, 201);
    EXPECT_EQ(cursor.total_charge, 200);
    EXPECT_EQ(store.pages.size(), 3); // two key chunks and one cursor
    auto const tail = decode_cache_chunk(
        ACCOUNT_RING,
        store.pages.at(cache_ring_key(ACCOUNT_RING, CacheRingPart::records, 2)),
        2);
    EXPECT_EQ(tail.records.size(), 8);
}

TEST(CacheRing, shared_cursor_coalesces_and_preserves_idle_ring)
{
    RingStore store;
    auto const key = cache_ring_key(ACCOUNT_RING, CacheRingPart::cursor);
    for (bool const storage_first : {false, true}) {
        CacheRingWriter accounts{ACCOUNT_RING, store.reader()};
        CacheRingWriter storage{STORAGE_RING, store.reader()};
        for (uint64_t i = 1; i <= 400; ++i) {
            accounts.append(record(i));
            storage.append(record(i, 2));
        }
        CachePageUpdates updates;
        (storage_first ? storage : accounts).finish(updates);
        (storage_first ? accounts : storage).finish(updates);
        size_t cursors = 0;
        for (auto const &[k, page] : updates) {
            cursors +=
                k.bytes[2] == static_cast<uint8_t>(CacheRingPart::cursor);
            store.pages[k] = page;
        }
        EXPECT_EQ(cursors, 1);
        EXPECT_LE(store.pages.at(key).size(), 6);
        EXPECT_EQ(
            read_cache_cursor(ACCOUNT_RING, store.reader()), accounts.cursor());
        EXPECT_EQ(
            read_cache_cursor(STORAGE_RING, store.reader()), storage.cursor());
    }
    auto const saved = read_cache_cursor(STORAGE_RING, store.reader());
    CacheRingWriter accounts{ACCOUNT_RING, store.reader()};
    accounts.append(record(999));
    store.save(accounts);
    EXPECT_EQ(read_cache_cursor(STORAGE_RING, store.reader()), saved);
    CacheRingWriter idle{STORAGE_RING, store.reader()};
    EXPECT_TRUE(idle.finish().empty());
}

TEST(CacheRing, charges_expire_whole_indices_and_wrap)
{
    CacheRingConfig const config{CacheRingKind::storage, 2, 8, 10, 5};
    RingStore store;
    uint64_t last_floor = 1;
    for (uint64_t n = 1; n <= 100; ++n) {
        CacheRingWriter writer{config, store.reader()};
        writer.append(record(n, static_cast<uint8_t>(n % 3 + 1)));
        auto const cursor = writer.cursor();
        EXPECT_LE(cursor.total_charge - cursor.floor_charge, 10);
        EXPECT_GE(cursor.view.floor, last_floor);
        EXPECT_EQ(cursor.view.floor % 2, 1);
        last_floor = cursor.view.floor;
        store.save(writer);
        uint64_t charge = 0;
        uint64_t records = 0;
        visit_cache_ring(
            config,
            store.reader(),
            [&](auto const &r, uint64_t stamp, bool dead) {
                charge += r.weight;
                ++records;
                EXPECT_TRUE(cache_stamp_cached(stamp, cursor.view));
                EXPECT_FALSE(dead);
            });
        EXPECT_EQ(charge, cursor.total_charge - cursor.floor_charge);
        EXPECT_EQ(records, cursor.view.next - cursor.view.floor);
        EXPECT_LE(store.pages.size(), 17);
    }
}

TEST(CacheRing, deletion_coalesces_without_refund_and_suppresses_older_record)
{
    CacheRingConfig const config{CacheRingKind::accounts, 4, 8, 10, 5};
    RingStore store;
    {
        CacheRingWriter writer{config, store.reader()};
        writer.append(record(1));
        writer.append(record(1)); // renewal
        writer.append(record(2));
        writer.append(record(3));
        store.save(writer);
    }
    auto const before = read_cache_cursor(config, store.reader());
    auto const original_chunk =
        store.pages.at(cache_ring_key(config, CacheRingPart::records, 1));
    {
        CacheRingWriter writer{config, store.reader()};
        EXPECT_TRUE(writer.erase(2));
        EXPECT_FALSE(writer.erase(2));
        EXPECT_TRUE(writer.erase(4));
        EXPECT_FALSE(writer.erase(0));
        EXPECT_FALSE(writer.erase(5));
        EXPECT_EQ(writer.cursor(), before);
        auto updates = writer.finish();
        EXPECT_EQ(updates.size(), 1); // only the record chunk changes
        EXPECT_TRUE(updates.contains(
            cache_ring_key(config, CacheRingPart::records, 1)));
        for (auto &[k, v] : updates) {
            store.pages[k] = std::move(v);
        }
    }
    EXPECT_NE(
        store.pages.at(cache_ring_key(config, CacheRingPart::records, 1)),
        original_chunk);
    std::map<Address, uint64_t> stamps;
    visit_cache_ring(
        config, store.reader(), [&](auto const &r, uint64_t stamp, bool dead) {
            Address key;
            std::memcpy(key.bytes, r.key.bytes, 20);
            if (dead) {
                stamps.erase(key);
            }
            else {
                stamps[key] = stamp;
            }
        });
    EXPECT_FALSE(stamps.contains(addr_of(1)));
    EXPECT_EQ(stamps.at(addr_of(2)), 3);
    // Later admission wins. Physical wrap resets old deletion bits.
    for (uint64_t i = 5; i <= 20; ++i) {
        CacheRingWriter writer{config, store.reader()};
        writer.append(record(1));
        store.save(writer);
    }
    visit_cache_ring(
        config, store.reader(), [&](auto const &, uint64_t, bool dead) {
            EXPECT_FALSE(dead);
        });
}

TEST(CacheRing, lazy_renewal_tracks_capacity_and_rings_are_independent)
{
    CacheRingConfig const a{CacheRingKind::accounts, 2, 8, 10, 5};
    CacheRingConfig const s{CacheRingKind::storage, 2, 8, 10, 5};
    RingStore store;
    CacheRingWriter accounts{a, store.reader()};
    accounts.append(record(1));
    store.save(accounts);
    CacheRingWriter storage{s, store.reader()};
    storage.append(record(1, 2));
    storage.append(record(2, 2));
    EXPECT_FALSE(cache_stamp_stale(1, storage.view()));
    storage.append(record(3, 1));
    EXPECT_TRUE(cache_stamp_stale(1, storage.view()));
    EXPECT_FALSE(cache_stamp_stale(3, storage.view()));
    store.save(storage);
    EXPECT_EQ(read_cache_cursor(a, store.reader()).view.refresh, 1);
}

TEST(CacheSelection, full_page_quota_deferred_candidates_and_canonical_order)
{
    mpt::Db db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb tdb{db, true, true, SMALL_CACHE};
    auto const c = addr_of(1);
    StateDeltas initial;
    add_account_change(initial, c, 0, std::nullopt, Account{.nonce = 1});
    for (uint64_t i = 0; i < 128; ++i) {
        add_slot(
            initial, c, store_be_as<bytes32_t>(uint256_t{i}), {}, VALUE, 0);
    }
    commit_block(tdb, 1, initial, {});
    StateDeltas reads;
    add_account(reads, c, 0);
    add_slot(reads, c, bytes32_t{}, VALUE, VALUE, 0);
    BlockStampCandidates candidates(2);
    candidates[0].charged_gas = 21000; // 10 credits cannot hold a 128-slot page
    candidates[0].accounts.push_back(c);
    candidates[0].storage.emplace_back(c, bytes32_t{});
    candidates[1] = candidates[0];
    candidates[1].charged_gas = 256000; // full page fits after account dedup
    StampContext const ctx{.candidates = &candidates, .db = &tdb};
    PageCommitBuilder builder(2, tdb, &ctx);
    builder.add_state_deltas(reads);
    auto const post = builder.take_proposal_post_state();
    EXPECT_EQ(post.account_stamps.at(c), 1);
    StorageKey const key{c, INC, bytes32_t{}};
    EXPECT_EQ(post.storage_stamps.at(key), 1);
    EXPECT_EQ(post.storage.at(key).size(), 128);
    commit_block(tdb, 2, reads, candidates);
    uint64_t stamp = 0;
    EXPECT_EQ(
        tdb.read_storage_stamped(
            c, INC, store_be_as<bytes32_t>(uint256_t{127}), stamp),
        VALUE);
    EXPECT_EQ(stamp, 1);
    TrieDb restarted{db, true, true, SMALL_CACHE};
    restarted.reset_root(tdb.get_root(), 2);
    auto rebuilt = restarted.rebuild_stamp_cache();
    EXPECT_EQ(rebuilt.pages, 1);
    EXPECT_EQ(rebuilt.slots, 128);
    EXPECT_EQ(
        restarted.read_storage_stamped(c, INC, bytes32_t{}, stamp), VALUE);
    EXPECT_EQ(stamp, 1);
}

TEST(
    CacheSelection,
    allowance_is_per_transaction_and_sort_ignores_encounter_order)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db, true, true, SMALL_CACHE};
    StateDeltas reads;
    BlockStampCandidates candidates(2);
    for (uint64_t i = 1; i <= 30; ++i) {
        add_account(reads, addr_of(i), 0);
        for (auto &tx : candidates) {
            tx.accounts.push_back(addr_of(i));
        }
    }
    for (auto &tx : candidates) {
        tx.charged_gas = 21000;
    }
    auto build = [&] {
        StampContext const ctx{.candidates = &candidates, .db = &tdb};
        CommitBuilder builder(1, &ctx);
        builder.add_state_deltas(reads);
        return builder.take_proposal_post_state();
    };
    auto first = build();
    EXPECT_EQ(first.account_stamps.size(), 20);
    for (auto &tx : candidates) {
        std::reverse(tx.accounts.begin(), tx.accounts.end());
    }
    auto second = build();
    EXPECT_EQ(first.account_stamps, second.account_stamps);
    for (auto &tx : candidates) {
        tx.charged_gas = 1999;
    }
    EXPECT_TRUE(build().account_stamps.empty());
}

TEST(CacheBootstrap, lazy_writes_growth_death_and_reentry)
{
    mpt::Db db{std::make_unique<MonadInMemoryMachine>()};
    DbCacheSizes const sizes{1000, 1024 * 1024, 0};
    TrieDb tdb{db, true, true, sizes};
    vm::VM vm;
    auto const c = addr_of(1);
    bytes32_t const slot{};
    auto const neighbor = store_be_as<bytes32_t>(uint256_t{1});
    Account const account{.nonce = 1};
    StateDeltas initial;
    add_account_change(initial, c, 0, std::nullopt, account);
    add_slot(initial, c, slot, {}, VALUE, 0);
    commit_block(tdb, 1, initial, {});
    StateDeltas reads;
    add_account(reads, c, 0, account);
    add_slot(reads, c, slot, VALUE, VALUE, 0);
    BlockStampCandidates candidates(1);
    candidates[0].charged_gas = 100000;
    candidates[0].accounts.push_back(c);
    candidates[0].storage.emplace_back(c, slot);
    commit_block(tdb, 2, reads, candidates);
    for (uint64_t n = 3; n <= 7; ++n) {
        StateDeltas changes;
        uint64_t astamp = 0, sstamp = 0;
        auto acct = tdb.read_account_stamped(c, astamp);
        auto const pre = tdb.read_storage_stamped(c, INC, slot, sstamp);
        add_account(changes, c, astamp, acct);
        if (n == 3) { // fresh growth retains original charge and stamp
            add_slot(changes, c, neighbor, {}, VALUE, sstamp);
        }
        else if (n == 4) { // entire page dies
            add_slot(changes, c, slot, pre, {}, sstamp);
            add_slot(changes, c, neighbor, VALUE, {}, sstamp);
        }
        else { // recreation inherits the retained stamp without re-admission
            add_slot(changes, c, slot, pre, VALUE, sstamp);
        }
        BlockStampCandidates txs(1);
        txs[0].charged_gas = 100000;
        txs[0].written_storage.emplace_back(c, n == 3 ? neighbor : slot);
        if (n == 6) {
            txs[0].storage.emplace_back(c, slot);
        }
        commit_block(tdb, n, changes, txs);
        TrieDb restarted{db, true, true, sizes};
        restarted.reset_root(tdb.get_root(), n);
        auto rebuilt = restarted.rebuild_stamp_cache();
        EXPECT_EQ(rebuilt.pages, n == 4 ? 0 : 1);
        for (auto *view : {&tdb, &restarted}) {
            uint64_t stamp = 99;
            view->read_storage_stamped(c, INC, slot, stamp);
            EXPECT_EQ(stamp, 1) << n;
            EXPECT_EQ(view->read_account_stamped(c, stamp), account);
            EXPECT_EQ(stamp, 1);
            BlockState block{*view, vm, nullptr, true};
            block.set_pricing_block(n + 1);
            State state{block, Incarnation{n + 1, 1}};
            // Access an empty slot on the page: only a completely empty
            // page is cold, even when negative values have been evicted.
            EXPECT_EQ(
                state.access_storage_tier<MonadTraits<MONAD_NEXT>>(
                    c, store_be_as<bytes32_t>(uint256_t{2})),
                n == 4 ? vm::Host::AccessTier::cold
                       : vm::Host::AccessTier::cached);
        }
    }
}

TEST(CacheFinalization, selected_values_upsert_without_readthrough_residency)
{
    DbCache cache{true, 3, 1024, 2};
    cache.set_block_and_prefix(0, {});
    auto const c = addr_of(1);
    cache.insert_account(
        c, Account{.nonce = 1}); // valued read misses aren't admitted
    std::optional<Account> result;
    EXPECT_NE(cache.try_read_account(c, result), CacheReadStatus::Hit);
    ProposalPostState post;
    post.accounts[c] = Account{.nonce = 1};
    post.account_stamps[c] = 1;
    StorageKey const key{c, INC, key_of(1)};
    post.storage[key] = storage_page_t{VALUE};
    post.storage_stamps[key] = 1;
    post.cache_pricing = {{1, 2, 1}, {1, 2, 1}};
    post.cache_updated = true;
    cache.update_proposal_state(std::move(post), 1, bytes32_t{1});
    cache.on_finalize(1, bytes32_t{1});
    EXPECT_TRUE(cache.account_has_stamp(c, 1));
    EXPECT_TRUE(cache.storage_has_stamp(key, 1));
    for (uint64_t i = 2; i < 100; ++i) {
        cache.insert_account(addr_of(i), std::nullopt);
        cache.insert_storage_page(c, INC, key_of(i), {});
    }
    EXPECT_TRUE(cache.account_has_stamp(c, 1));
    EXPECT_TRUE(cache.storage_has_stamp(key, 1));
}

TEST(CacheFinalization, key_history_survives_negative_eviction_and_expires)
{
    DbCache cache{true, 10, 1024 * 1024, 0};
    auto const address = addr_of(1);
    StorageKey const key{address, INC, key_of(1)};
    ProposalPostState bootstrap;
    bootstrap.cache_updated = true;
    bootstrap.cache_pricing = {{1, 2, 1}, {1, 2, 1}};
    bootstrap.account_stamps[address] = 1;
    bootstrap.storage_stamps[key] = 1;
    bootstrap.accounts[address] = std::nullopt;
    bootstrap.storage[key] = {};
    cache.rebuild_stamps(bootstrap);
    cache.set_block_and_prefix(0, {});
    uint64_t stamp = 0;
    std::optional<Account> account;
    bytes32_t value;
    EXPECT_EQ(
        cache.try_read_account(address, account, &stamp),
        CacheReadStatus::MissResolved);
    EXPECT_EQ(stamp, 1);
    EXPECT_EQ(
        cache.try_read_storage(address, INC, key_of(1), 0, value, &stamp),
        CacheReadStatus::MissResolved);
    EXPECT_EQ(stamp, 1);

    ProposalPostState recreated;
    recreated.cache_updated = true;
    recreated.cache_pricing = bootstrap.cache_pricing;
    recreated.accounts[address] = Account{.nonce = 1};
    recreated.storage[key] = storage_page_t{VALUE};
    cache.update_proposal_state(std::move(recreated), 1, bytes32_t{1});
    EXPECT_FALSE(cache.on_finalize(1, bytes32_t{1}));
    cache.set_block_and_prefix(1, {});
    EXPECT_TRUE(cache.account_has_stamp(address, 1));
    EXPECT_TRUE(cache.storage_has_stamp(key, 1));

    ProposalPostState expired;
    expired.cache_updated = true;
    expired.cache_pricing = {{2, 2, 2}, {2, 2, 2}};
    cache.update_proposal_state(std::move(expired), 2, bytes32_t{2});
    EXPECT_FALSE(cache.on_finalize(2, bytes32_t{2}));
    cache.set_block_and_prefix(2, {});
    cache.try_read_account(address, account, &stamp);
    EXPECT_EQ(stamp, 0);
    cache.try_read_storage(address, INC, key_of(1), 0, value, &stamp);
    EXPECT_EQ(stamp, 0);
}

TEST(CacheRing, key_history_renewal_survives_retirement_of_older_record)
{
    StampIndex<Address> index;
    decltype(ProposalPostState::account_stamps) updates;
    updates[addr_of(1)] = 1;
    index.update({1, 2, 1}, updates);
    updates[addr_of(1)] = 2;
    index.update({1, 3, 1}, updates);
    updates.clear();
    index.update({2, 3, 2}, updates);
    EXPECT_EQ(index.find(addr_of(1)), 2);
    index.update({3, 3, 3}, updates);
    EXPECT_EQ(index.find(addr_of(1)), 0);
}

TEST(CacheRing, compact_history_matches_reference_across_renewal_and_expiry)
{
    StampIndex<Address> index;
    decltype(ProposalPostState::account_stamps) updates, reference;
    std::mt19937 random{42};
    for (uint64_t stamp = 1; stamp <= 1000; ++stamp) {
        CacheRingView const view{
            stamp > 17 ? stamp - 17 : 1,
            stamp + 1,
            stamp > 17 ? stamp - 17 : 1};
        auto const key = addr_of(random() % 31);
        reference[key] = stamp;
        updates.clear();
        updates[key] = stamp;
        index.update(view, updates);
        for (uint64_t k = 0; k < 31; ++k) {
            auto const it = reference.find(addr_of(k));
            uint64_t const expected =
                it != reference.end() && cache_stamp_cached(it->second, view)
                    ? it->second
                    : 0;
            EXPECT_EQ(index.find(addr_of(k)), expected);
        }
    }
}

TEST(CacheFinalization, reentry_does_not_hide_expired_eviction_victim)
{
    StampCache<Address, std::optional<Account>, BytesHashCompare<Address>>
        cache{2, 3, 1};
    cache.insert(addr_of(1), Account{}, 1, false, 1);
    cache.insert(addr_of(2), Account{}, 1, false, 2);
    cache.insert(addr_of(1), std::nullopt, 1, true);
    cache.insert(addr_of(1), Account{}, 1, false, 1);
    cache.set_evict_floor(2);
    cache.insert(addr_of(3), Account{}, 1, false, 3);
    decltype(cache)::ConstAccessor acc;
    EXPECT_FALSE(cache.find(acc, addr_of(1)));
    EXPECT_TRUE(cache.find(acc, addr_of(2)));
}

TEST(CacheFinalization, expiry_evicts_oldest_values_and_upserts_atomically)
{
    StampCache<Address, std::optional<Account>, BytesHashCompare<Address>>
        cache{3, 4, 2};
    for (uint64_t i = 1; i <= 3; ++i) {
        cache.insert(addr_of(i), Account{.nonce = i}, 1, false, i);
    }
    cache.insert(addr_of(9), std::nullopt, 1, true);
    cache.set_evict_floor(2);
    cache.insert(addr_of(4), Account{.nonce = 4}, 1, false, 4);
    decltype(cache)::ConstAccessor acc;
    EXPECT_FALSE(cache.find(acc, addr_of(1)));
    ASSERT_TRUE(cache.find(acc, addr_of(4)));
    EXPECT_EQ(cache.stamp_of(acc), 4);
    acc.release();
    EXPECT_EQ(cache.approx_weight(), 3);
    cache.clear_stamp(addr_of(2));
    cache.insert(addr_of(2), std::nullopt, 1, true);
    cache.insert(addr_of(5), Account{.nonce = 5}, 1, false, 5);
    ASSERT_TRUE(cache.find(acc, addr_of(3)));
    EXPECT_EQ(cache.stamp_of(acc), 3);
}

TEST(
    CacheFinalization, concurrent_negative_reads_and_insertions_preserve_stamps)
{
    StampCache<Address, std::optional<Account>, BytesHashCompare<Address>>
        cache{16, 32, 16};
    for (uint64_t i = 1; i <= 16; ++i) {
        cache.insert(addr_of(i), Account{.nonce = i}, 1, false, i);
    }
    std::vector<std::thread> threads;
    for (uint64_t t = 0; t < 4; ++t) {
        threads.emplace_back([&, t] {
            for (uint64_t i = 0; i < 2000; ++i) {
                cache.insert(
                    addr_of(100 + t * 2000 + i), std::nullopt, 1, true);
                decltype(cache)::ConstAccessor acc;
                ASSERT_TRUE(cache.find(acc, addr_of(i % 16 + 1)));
                EXPECT_EQ(cache.stamp_of(acc), i % 16 + 1);
            }
        });
    }
    for (auto &thread : threads) {
        thread.join();
    }
    EXPECT_LE(cache.size(), 32);
    EXPECT_LE(cache.negative_count(), 16);
    EXPECT_EQ(cache.approx_weight(), 16);
}

// Run explicitly for the physical-capacity measurement, outside replay timing.
TEST(CacheFinalization, DISABLED_five_million_slots_and_negative_pressure)
{
    StampCache<StorageKey, storage_page_t, BytesHashCompare<StorageKey>> cache{
        1024ULL * 1024 * 1024, 10'000'000, 2'000'000};
    auto const page = storage_page_t{VALUE};
    for (uint64_t i = 1; i <= 5'000'000; ++i) {
        cache.insert(
            StorageKey{addr_of(1), INC, key_of(i)},
            page,
            static_cast<uint32_t>(page.byte_size()),
            false,
            i);
    }
    for (uint64_t i = 5'000'001; i <= 7'100'000; ++i) {
        cache.insert(
            StorageKey{addr_of(1), INC, key_of(i)},
            {},
            static_cast<uint32_t>(sizeof(storage_page_t)),
            true);
    }
    EXPECT_EQ(cache.approx_weight(), 5'000'000 * page.byte_size());
    EXPECT_EQ(cache.negative_count(), 2'000'000);
    EXPECT_EQ(cache.size(), 7'000'000);
    for (uint64_t i = 1; i <= 5'000'000; ++i) {
        decltype(cache)::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, StorageKey{addr_of(1), INC, key_of(i)}));
        ASSERT_EQ(cache.stamp_of(acc), i);
        ASSERT_EQ(acc->second.value_, page);
    }
}

TEST(CacheProposals, stamps_cross_value_lookup_depth_and_inherit_finalized_base)
{
    DbCache cache{true, 100, 1024 * 1024, 10};
    auto const c = addr_of(1);
    StorageKey const key{c, INC, key_of(1)};
    auto selected = [&](uint64_t stamp) {
        ProposalPostState post;
        post.accounts[c] = Account{.nonce = 1};
        post.storage[key] = storage_page_t{VALUE};
        post.account_stamps[c] = stamp;
        post.storage_stamps[key] = stamp;
        post.cache_updated = true;
        post.cache_pricing = {{1, stamp + 1, 1}, {1, stamp + 1, 1}};
        return post;
    };
    cache.set_block_and_prefix(0, {});
    cache.update_proposal_state(selected(1), 1, bytes32_t{1});
    EXPECT_FALSE(cache.on_finalize(1, bytes32_t{1}));
    cache.set_block_and_prefix(1, {});
    for (uint64_t n = 2; n <= 10; ++n) {
        cache.update_proposal_state({}, n, bytes32_t{n});
    }
    uint64_t stamp = 0;
    std::optional<Account> account;
    bytes32_t value;
    EXPECT_EQ(
        cache.try_read_account(c, account, &stamp),
        CacheReadStatus::MissTruncated);
    EXPECT_EQ(stamp, 1);
    EXPECT_EQ(
        cache.try_read_storage(c, INC, key_of(1), 0, value, &stamp),
        CacheReadStatus::MissTruncated);
    EXPECT_EQ(stamp, 1);
    cache.update_proposal_state(selected(2), 11, bytes32_t{11});
    for (uint64_t n = 12; n <= 20; ++n) {
        cache.update_proposal_state({}, n, bytes32_t{n});
    }
    EXPECT_EQ(
        cache.try_read_account(c, account, &stamp),
        CacheReadStatus::MissTruncated);
    EXPECT_EQ(stamp, 2);
    EXPECT_EQ(
        cache.try_read_storage(c, INC, key_of(1), 0, value, &stamp),
        CacheReadStatus::MissTruncated);
    EXPECT_EQ(stamp, 2);
    for (uint64_t n = 21; n <= 115; ++n) {
        cache.update_proposal_state({}, n, bytes32_t{n});
    }
    cache.try_read_account(c, account, &stamp);
    EXPECT_EQ(stamp, CACHE_STAMP_UNKNOWN); // TrieDb resolves this from the log
    EXPECT_TRUE(
        cache.on_finalize(2, bytes32_t{2})); // requests bootstrap after pruning
}

TEST(CacheRing, pruned_proposal_fallback_resolves_latest_record_and_deletion)
{
    RingStore store;
    {
        CacheRingWriter writer{STORAGE_RING, store.reader()};
        writer.append(record(1));
        writer.append(record(1));
        writer.append(record(2));
        writer.erase(2);
        store.save(writer);
    }
    EXPECT_EQ(
        resolve_cache_stamp(STORAGE_RING, store.reader(), record(1).key), 0);
    EXPECT_EQ(
        resolve_cache_stamp(STORAGE_RING, store.reader(), record(2).key), 3);
    {
        CacheRingWriter writer{STORAGE_RING, store.reader()};
        writer.append(record(1));
        store.save(writer);
    }
    EXPECT_EQ(
        resolve_cache_stamp(STORAGE_RING, store.reader(), record(1).key), 4);
}

TEST(CacheFinalization, retired_selection_still_updates_resident_values)
{
    DbCache cache{true, 10, 1024, 2};
    Address const c = addr_of(1), d = addr_of(2);
    StorageKey const key{c, INC, key_of(1)}, other{d, INC, key_of(2)};
    ProposalPostState initial;
    initial.accounts[c] = Account{.nonce = 1};
    initial.storage[key] = storage_page_t{VALUE};
    initial.account_stamps[c] = 1;
    initial.storage_stamps[key] = 1;
    initial.cache_updated = true;
    initial.cache_pricing = {{1, 2, 1}, {1, 2, 1}};
    cache.set_block_and_prefix(0, {});
    cache.update_proposal_state(std::move(initial), 1, bytes32_t{1});
    EXPECT_FALSE(cache.on_finalize(1, bytes32_t{1}));
    cache.set_block_and_prefix(1, {});
    ProposalPostState post;
    post.accounts[c] = Account{.nonce = 2};
    post.storage[key] = storage_page_t{key_of(99)};
    post.account_stamps[c] = 2;
    post.storage_stamps[key] = 2;
    post.accounts[d] = Account{.nonce = 3};
    post.storage[other] = storage_page_t{VALUE};
    post.account_stamps[d] = 3;
    post.storage_stamps[other] = 3;
    post.cache_updated = true;
    post.cache_pricing = {{3, 4, 3}, {3, 4, 3}};
    cache.update_proposal_state(std::move(post), 2, bytes32_t{2});
    EXPECT_FALSE(cache.on_finalize(2, bytes32_t{2}));
    cache.set_block_and_prefix(2, {});
    std::optional<Account> account;
    bytes32_t value;
    uint64_t stamp = 99;
    EXPECT_EQ(cache.try_read_account(c, account, &stamp), CacheReadStatus::Hit);
    EXPECT_EQ(account->nonce, 2);
    EXPECT_FALSE(cache_stamp_cached(stamp, CacheRingView{3, 4, 3}));
    EXPECT_EQ(
        cache.try_read_storage(c, INC, key_of(1), 0, value, &stamp),
        CacheReadStatus::Hit);
    EXPECT_EQ(value, key_of(99));
    EXPECT_FALSE(cache_stamp_cached(stamp, CacheRingView{3, 4, 3}));
    EXPECT_TRUE(cache.account_has_stamp(d, 3));
    EXPECT_TRUE(cache.storage_has_stamp(other, 3));
}

TEST(CacheFinalization, weight_uses_compacted_resident_page)
{
    storage_page_t page;
    for (uint8_t i = 0; i < 128; ++i) {
        page.set(i, VALUE);
    }
    for (uint8_t i = 1; i < 128; ++i) {
        page.set(i, {});
    }
    ASSERT_GT(page.byte_size(), sizeof(storage_page_t));
    ASSERT_EQ(page.size(), 1);
    StampCache<StorageKey, storage_page_t, BytesHashCompare<StorageKey>> cache{
        2 * sizeof(storage_page_t), 2, 0};
    for (uint64_t i = 1; i <= 2; ++i) {
        StorageKey const key{addr_of(1), INC, key_of(i)};
        cache.insert(
            key, page, static_cast<uint32_t>(page.byte_size()), false, i);
        decltype(cache)::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, key));
        EXPECT_EQ(acc->second.value_.byte_size(), sizeof(storage_page_t));
        EXPECT_EQ(cache.stamp_of(acc), i);
    }
    EXPECT_EQ(cache.approx_weight(), 2 * sizeof(storage_page_t));
}
