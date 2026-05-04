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

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/result.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <utility>

using namespace monad::mpt;
using namespace monad::test;
using namespace monad::literals;

namespace
{

    // Helper: create an update inserting key=value
    Update make_kv(monad::byte_string_view key, monad::byte_string_view value)
    {
        return make_update(key, value);
    }

    // Helper: look up a key from a root on the given Db and return the value
    monad::Result<monad::byte_string>
    db_get(Db &db, NodeCursor const &root, NibblesView key, uint64_t version)
    {
        auto const res = db.find(root, key, version);
        if (res.has_value()) {
            return monad::byte_string{res.value().node->value()};
        }
        return monad::mpt::DbError(res.error().value());
    }

    struct DualTimelineFixture : public ::testing::Test
    {
        std::filesystem::path const dbname{create_temp_file(8)};
        StateMachineAlwaysMerkle primary_machine;
        StateMachineAlwaysMerkle secondary_machine;
        OnDiskDbConfig config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};
        Db db{primary_machine, config};
        std::optional<Db> secondary_db;

        Node::SharedPtr primary_root;
        Node::SharedPtr secondary_root;

        ~DualTimelineFixture()
        {
            std::filesystem::remove(dbname);
        }

        Db &db_for(timeline_id tid)
        {
            if (tid == timeline_id::secondary) {
                MONAD_ASSERT(secondary_db.has_value());
                return *secondary_db;
            }
            return db;
        }

        void activate_secondary(uint64_t fork_version)
        {
            secondary_db.emplace(db.activate_secondary_timeline(
                secondary_machine, fork_version));
        }

        void deactivate_secondary()
        {
            secondary_db.reset();
            db.deactivate_secondary_timeline();
        }

        void promote_secondary()
        {
            secondary_db.reset();
            db.promote_secondary_to_primary();
        }

        // Close and reopen the primary Db against the same file, as
        // production would after promote.
        void reopen_primary_with(StateMachine &machine)
        {
            {
                Db const expired = std::move(db);
            }
            OnDiskDbConfig reopen_config = config;
            reopen_config.append = true;
            db = Db{machine, reopen_config};
        }

        Node::SharedPtr upsert_kv(
            Node::SharedPtr root, monad::byte_string_view key,
            monad::byte_string_view value, uint64_t version,
            timeline_id tid = timeline_id::primary)
        {
            auto u = make_kv(key, value);
            UpdateList ul;
            ul.push_front(u);
            return db_for(tid).upsert(std::move(root), std::move(ul), version);
        }
    };

    // -------------------------------------------------------------------
    // Test: Activate and deactivate without any upserts on secondary
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, activate_deactivate_empty)
    {
        // Seed primary with a few versions
        auto const k1 = 0x11111111_bytes;
        auto const k2 = 0x22222222_bytes;
        primary_root = upsert_kv(primary_root, k1, k1, 0);
        primary_root = upsert_kv(primary_root, k2, k2, 1);
        ASSERT_NE(primary_root, nullptr);

        // Activate secondary at version 2 (after primary has 0,1)
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));
        activate_secondary(2);
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        // Deactivate without doing anything on secondary
        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));

        // Primary should be unaffected
        auto const res = db_get(db, primary_root, NibblesView{k1}, 1);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), k1);
    }

    // -------------------------------------------------------------------
    // Test: open_secondary_timeline attaches to an active secondary
    // without modifying metadata; returns nullopt when inactive.
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, open_secondary_timeline_factory)
    {
        // No secondary yet
        EXPECT_FALSE(db.open_secondary_timeline(secondary_machine).has_value());

        activate_secondary(0);

        // Drop the Db returned by activate_secondary_timeline — mimicking
        // a process restart where the secondary metadata persists on disk
        // but the secondary Db instance is gone.
        secondary_db.reset();
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        // Reattach via open_secondary_timeline
        auto reopened = db.open_secondary_timeline(secondary_machine);
        ASSERT_TRUE(reopened.has_value());

        // The reattached Db can upsert and read secondary data
        auto const k = 0xAAAAAAAA_bytes;
        auto u = make_update(k, k);
        UpdateList ul;
        ul.push_front(u);
        auto const sroot = reopened->upsert(nullptr, std::move(ul), 0);
        ASSERT_NE(sroot, nullptr);
        auto const res = db_get(*reopened, sroot, NibblesView{k}, 0);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), k);

        // Destroy the reopened Db, then deactivate via primary
        reopened.reset();
        db.deactivate_secondary_timeline();

        // After deactivate, open returns nullopt again
        EXPECT_FALSE(db.open_secondary_timeline(secondary_machine).has_value());
    }

    // -------------------------------------------------------------------
    // Test: Seed primary, activate secondary, replay same updates on both
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, replay_identical_updates)
    {
        // Seed primary with versions 0-4
        auto const keys = std::array{
            0x11111111_bytes,
            0x22222222_bytes,
            0x33333333_bytes,
            0x44444444_bytes,
            0x55555555_bytes};

        for (uint64_t v = 0; v < keys.size(); v++) {
            primary_root = upsert_kv(primary_root, keys[v], keys[v], v);
            ASSERT_NE(primary_root, nullptr);
        }

        // Activate secondary at version 0
        activate_secondary(0);

        // Replay same updates on secondary timeline
        for (uint64_t v = 0; v < keys.size(); v++) {
            secondary_root = upsert_kv(
                secondary_root, keys[v], keys[v], v, timeline_id::secondary);
            ASSERT_NE(secondary_root, nullptr);
        }

        // Both timelines should have all 5 keys at their latest root
        for (auto const &key : keys) {
            auto const pres = db_get(db, primary_root, NibblesView{key}, 4);
            ASSERT_TRUE(pres.has_value()) << "primary missing key";
            EXPECT_EQ(pres.value(), key);

            auto const sres = db_get(
                db_for(timeline_id::secondary),
                secondary_root,
                NibblesView{key},
                4);
            ASSERT_TRUE(sres.has_value()) << "secondary missing key";
            EXPECT_EQ(sres.value(), key);
        }

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Concurrent updates — both timelines advance with different data
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, concurrent_updates_different_data)
    {
        // Seed primary with versions 0-2
        auto const seed_key = 0xAAAAAAAA_bytes;
        primary_root = upsert_kv(primary_root, seed_key, seed_key, 0);
        primary_root = upsert_kv(primary_root, seed_key, seed_key, 1);
        primary_root = upsert_kv(primary_root, seed_key, seed_key, 2);

        // Activate secondary at version 3
        activate_secondary(3);
        // Give secondary the same seed
        secondary_root = upsert_kv(
            secondary_root, seed_key, seed_key, 3, timeline_id::secondary);

        // Now advance both timelines with DIFFERENT keys at version 4+
        auto const primary_key = 0xBBBBBBBB_bytes;
        auto const secondary_key = 0xCCCCCCCC_bytes;

        for (uint64_t v = 3; v <= 5; v++) {
            primary_root = upsert_kv(primary_root, primary_key, primary_key, v);
            secondary_root = upsert_kv(
                secondary_root,
                secondary_key,
                secondary_key,
                v,
                timeline_id::secondary);
        }

        // Primary should have primary_key but NOT secondary_key
        auto const pres = db_get(db, primary_root, NibblesView{primary_key}, 5);
        ASSERT_TRUE(pres.has_value());
        EXPECT_EQ(pres.value(), primary_key);
        auto const pres2 =
            db_get(db, primary_root, NibblesView{secondary_key}, 5);
        EXPECT_FALSE(pres2.has_value());

        // Secondary should have secondary_key but NOT primary_key
        auto const sres = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{secondary_key},
            5);
        ASSERT_TRUE(sres.has_value());
        EXPECT_EQ(sres.value(), secondary_key);
        auto const sres2 = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{primary_key},
            5);
        EXPECT_FALSE(sres2.has_value());

        // Both should have the seed key
        auto const pseed = db_get(db, primary_root, NibblesView{seed_key}, 5);
        ASSERT_TRUE(pseed.has_value());
        auto const sseed = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{seed_key},
            5);
        ASSERT_TRUE(sseed.has_value());

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Primary ahead of secondary by several versions
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, primary_ahead_of_secondary)
    {
        // Seed primary with versions 0-9
        auto const k1 = 0x11111111_bytes;
        for (uint64_t v = 0; v < 10; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            primary_root = upsert_kv(primary_root, k1, val, v);
        }

        // Activate secondary at version 5 — primary is at version 9
        activate_secondary(5);

        // Secondary catches up from version 5 to 7 (still behind primary at 9)
        for (uint64_t v = 5; v <= 7; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            secondary_root =
                upsert_kv(secondary_root, k1, val, v, timeline_id::secondary);
        }

        // Primary is at version 9, secondary is at version 7
        auto const pres = db_get(db, primary_root, NibblesView{k1}, 9);
        ASSERT_TRUE(pres.has_value());
        EXPECT_EQ(pres.value()[0], 9);

        auto const sres = db_get(
            db_for(timeline_id::secondary), secondary_root, NibblesView{k1}, 7);
        ASSERT_TRUE(sres.has_value());
        EXPECT_EQ(sres.value()[0], 7);

        // Continue: primary advances to 12, secondary catches up to 12
        for (uint64_t v = 10; v <= 12; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            primary_root = upsert_kv(primary_root, k1, val, v);
        }
        for (uint64_t v = 8; v <= 12; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            secondary_root =
                upsert_kv(secondary_root, k1, val, v, timeline_id::secondary);
        }

        // Both at version 12 with same value
        auto const pres12 = db_get(db, primary_root, NibblesView{k1}, 12);
        ASSERT_TRUE(pres12.has_value());
        EXPECT_EQ(pres12.value()[0], 12);
        auto const sres12 = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{k1},
            12);
        ASSERT_TRUE(sres12.has_value());
        EXPECT_EQ(sres12.value()[0], 12);

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Promote secondary to primary
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, promote_secondary)
    {
        // Seed primary with versions 0-3
        auto const k1 = 0x11111111_bytes;
        auto const v1 = 0xAA_bytes;
        auto const k2 = 0x22222222_bytes;
        auto const v2 = 0xBB_bytes;

        primary_root = upsert_kv(primary_root, k1, v1, 0);
        primary_root = upsert_kv(primary_root, k2, v2, 1);
        primary_root = upsert_kv(primary_root, k1, v1, 2);
        primary_root = upsert_kv(primary_root, k2, v2, 3);

        // Activate secondary at version 2, replay
        activate_secondary(2);
        secondary_root =
            upsert_kv(secondary_root, k1, v1, 2, timeline_id::secondary);
        secondary_root =
            upsert_kv(secondary_root, k2, v2, 3, timeline_id::secondary);

        // Now advance both with version 4
        auto const k3 = 0x33333333_bytes;
        auto const v3_primary = 0xCC_bytes;
        auto const v3_secondary = 0xDD_bytes;
        primary_root = upsert_kv(primary_root, k3, v3_primary, 4);
        secondary_root = upsert_kv(
            secondary_root, k3, v3_secondary, 4, timeline_id::secondary);

        // Promote secondary to primary. This clears the primary Db's
        // StateMachine binding; callers must close and reopen with the
        // correct machine before further writes.
        promote_secondary();

        // Simulate production close+reopen: drop the current (now
        // machine-less) Db and reopen bound to secondary_machine, which
        // is the authoritative machine for what is now the primary trie.
        reopen_primary_with(secondary_machine);

        // After promotion:
        // - What was secondary is now primary (has v3_secondary for k3)
        // - What was primary is now secondary (has v3_primary for k3)
        // The in-memory root variables don't change — they're node
        // pointers into an on-disk trie whose metadata slot has swapped.
        EXPECT_TRUE(db.timeline_active(timeline_id::primary));
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        // The secondary root's data is accessible
        auto const sres = db_get(db, secondary_root, NibblesView{k3}, 4);
        ASSERT_TRUE(sres.has_value());
        EXPECT_EQ(sres.value(), v3_secondary);

        // The primary root's data is also accessible
        auto const pres = db_get(db, primary_root, NibblesView{k3}, 4);
        ASSERT_TRUE(pres.has_value());
        EXPECT_EQ(pres.value(), v3_primary);

        // After promotion+reopen, we can continue upserts on the new
        // primary (which was the secondary timeline).
        auto const k4 = 0x44444444_bytes;
        auto const v4 = 0xEE_bytes;
        secondary_root = upsert_kv(secondary_root, k4, v4, 5);
        ASSERT_NE(secondary_root, nullptr);

        auto const res4 = db_get(db, secondary_root, NibblesView{k4}, 5);
        ASSERT_TRUE(res4.has_value());
        EXPECT_EQ(res4.value(), v4);

        // Deactivate the old primary (now secondary)
        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));
    }

    // -------------------------------------------------------------------
    // Test: Multiple keys across many versions with concurrent timelines
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, many_versions_concurrent)
    {
        constexpr uint64_t N_VERSIONS = 20;

        // Build primary with N versions, each inserting a new key
        for (uint64_t v = 0; v < N_VERSIONS; v++) {
            monad::byte_string key(4, 0);
            key[0] = static_cast<uint8_t>(v >> 8);
            key[1] = static_cast<uint8_t>(v & 0xff);
            key[2] = 0x01; // primary marker
            primary_root = upsert_kv(primary_root, key, key, v);
            ASSERT_NE(primary_root, nullptr);
        }

        // Activate secondary at version N
        uint64_t const fork_version = N_VERSIONS;
        activate_secondary(fork_version);

        // Advance both timelines from fork_version to N_VERSIONS + 5
        for (uint64_t v = fork_version; v < N_VERSIONS + 5; v++) {
            monad::byte_string pkey(4, 0);
            pkey[0] = static_cast<uint8_t>(v >> 8);
            pkey[1] = static_cast<uint8_t>(v & 0xff);
            pkey[2] = 0x01; // primary
            primary_root = upsert_kv(primary_root, pkey, pkey, v);

            monad::byte_string skey(4, 0);
            skey[0] = static_cast<uint8_t>(v >> 8);
            skey[1] = static_cast<uint8_t>(v & 0xff);
            skey[2] = 0x02; // secondary
            secondary_root = upsert_kv(
                secondary_root, skey, skey, v, timeline_id::secondary);
        }

        uint64_t const final_version = N_VERSIONS + 4;

        // Verify primary has all primary keys
        for (uint64_t v = fork_version; v < N_VERSIONS + 5; v++) {
            monad::byte_string pkey(4, 0);
            pkey[0] = static_cast<uint8_t>(v >> 8);
            pkey[1] = static_cast<uint8_t>(v & 0xff);
            pkey[2] = 0x01;
            auto const res =
                db_get(db, primary_root, NibblesView{pkey}, final_version);
            ASSERT_TRUE(res.has_value()) << "primary missing key at v=" << v;
        }

        // Verify secondary has all secondary keys
        for (uint64_t v = fork_version; v < N_VERSIONS + 5; v++) {
            monad::byte_string skey(4, 0);
            skey[0] = static_cast<uint8_t>(v >> 8);
            skey[1] = static_cast<uint8_t>(v & 0xff);
            skey[2] = 0x02;
            auto const res = db_get(
                db_for(timeline_id::secondary),
                secondary_root,
                NibblesView{skey},
                final_version);
            ASSERT_TRUE(res.has_value()) << "secondary missing key at v=" << v;
        }

        // Primary should NOT have secondary-only keys
        {
            monad::byte_string skey(4, 0);
            skey[0] = 0;
            skey[1] = static_cast<uint8_t>(fork_version);
            skey[2] = 0x02;
            auto const res =
                db_get(db, primary_root, NibblesView{skey}, final_version);
            EXPECT_FALSE(res.has_value());
        }

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Activate at version 0 (edge case for the active_ flag)
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, activate_at_version_zero)
    {
        activate_secondary(0);
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        // Upsert on both
        auto const key = 0x12345678_bytes;
        primary_root = upsert_kv(primary_root, key, key, 0);
        secondary_root =
            upsert_kv(secondary_root, key, key, 0, timeline_id::secondary);

        ASSERT_NE(primary_root, nullptr);
        ASSERT_NE(secondary_root, nullptr);

        auto const pres = db_get(db, primary_root, NibblesView{key}, 0);
        ASSERT_TRUE(pres.has_value());
        auto const sres = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{key},
            0);
        ASSERT_TRUE(sres.has_value());

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Full lifecycle — activate, concurrent, promote, cleanup
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, full_lifecycle)
    {
        // Phase 1: Seed primary with versions 0-2
        auto const k1 = 0x11111111_bytes;
        primary_root = upsert_kv(primary_root, k1, k1, 0);
        primary_root = upsert_kv(primary_root, k1, 0xAA_bytes, 1);
        primary_root = upsert_kv(primary_root, k1, k1, 2);

        // Phase 2: Activate secondary at version 3
        activate_secondary(3);
        secondary_root =
            upsert_kv(secondary_root, k1, k1, 3, timeline_id::secondary);

        // Phase 3: Concurrent operation — both advance versions 4-6
        auto const k2 = 0x22222222_bytes;
        for (uint64_t v = 3; v <= 6; v++) {
            primary_root = upsert_kv(primary_root, k2, k2, v);
        }
        for (uint64_t v = 4; v <= 6; v++) {
            secondary_root =
                upsert_kv(secondary_root, k2, k2, v, timeline_id::secondary);
        }

        // Phase 4: Promote secondary, then reopen RWDb bound to the
        // secondary_machine (authoritative for the now-primary trie).
        promote_secondary();
        reopen_primary_with(secondary_machine);
        EXPECT_TRUE(db.timeline_active(timeline_id::primary));
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        // Phase 5: Continue operating on the new primary (was secondary)
        auto const k3 = 0x33333333_bytes;
        secondary_root = upsert_kv(secondary_root, k3, k3, 7);
        ASSERT_NE(secondary_root, nullptr);
        auto const res = db_get(db, secondary_root, NibblesView{k3}, 7);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value(), k3);

        // Phase 6: Deactivate old primary (now secondary)
        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));

        // New primary still works
        secondary_root = upsert_kv(secondary_root, k3, 0xFF_bytes, 8);
        ASSERT_NE(secondary_root, nullptr);
    }

    // -------------------------------------------------------------------
    // Test: load_root_for_version with timeline_id
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, load_root_for_version_by_timeline)
    {
        // Seed primary with versions 0-3
        auto const k1 = 0x11111111_bytes;
        for (uint64_t v = 0; v <= 3; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            primary_root = upsert_kv(primary_root, k1, val, v);
        }

        // Activate secondary at version 2, upsert versions 2-3
        activate_secondary(2);
        auto const k2 = 0x22222222_bytes;
        for (uint64_t v = 2; v <= 3; v++) {
            auto const val =
                monad::byte_string(4, static_cast<uint8_t>(v + 10));
            secondary_root =
                upsert_kv(secondary_root, k2, val, v, timeline_id::secondary);
        }

        // load_root_for_version on primary returns the primary root
        auto const loaded_primary = db.load_root_for_version(3);
        ASSERT_NE(loaded_primary, nullptr);
        auto const res = db_get(db, loaded_primary, NibblesView{k1}, 3);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value()[0], 3);

        // load_root_for_version on secondary returns the secondary root
        auto const loaded_secondary = secondary_db->load_root_for_version(3);
        ASSERT_NE(loaded_secondary, nullptr);
        auto const res2 =
            db_get(*secondary_db, loaded_secondary, NibblesView{k2}, 3);
        ASSERT_TRUE(res2.has_value());
        EXPECT_EQ(res2.value()[0], 13);

        // Primary root should NOT have k2 (secondary-only key)
        auto const res3 = db_get(db, loaded_primary, NibblesView{k2}, 3);
        EXPECT_FALSE(res3.has_value());

        // Secondary root should NOT have k1 (primary-only key)
        auto const res4 =
            db_get(*secondary_db, loaded_secondary, NibblesView{k1}, 3);
        EXPECT_FALSE(res4.has_value());

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Two TrieDb-like instances sharing one mpt::Db
    // Demonstrates the pattern for execution-layer dual-timeline
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, two_independent_root_trees)
    {
        // Build a shared key set on primary: versions 0-4
        auto const shared_key = 0xAAAAAAAA_bytes;
        for (uint64_t v = 0; v <= 4; v++) {
            primary_root = upsert_kv(primary_root, shared_key, shared_key, v);
        }

        // Activate secondary at version 5
        activate_secondary(5);

        // Each "TrieDb" instance holds its own root and advances independently
        // Primary TrieDb: inserts primary-only data at versions 5-7
        auto const pk = 0xBBBBBBBB_bytes;
        for (uint64_t v = 5; v <= 7; v++) {
            primary_root = upsert_kv(primary_root, pk, pk, v);
        }

        // Secondary TrieDb: inserts secondary-only data at versions 5-7
        auto const sk = 0xCCCCCCCC_bytes;
        for (uint64_t v = 5; v <= 7; v++) {
            secondary_root =
                upsert_kv(secondary_root, sk, sk, v, timeline_id::secondary);
        }

        // Load roots from the ring at version 7 — each gets its own root
        auto const p7 = db.load_root_for_version(7);
        auto const s7 = secondary_db->load_root_for_version(7);
        ASSERT_NE(p7, nullptr);
        ASSERT_NE(s7, nullptr);
        EXPECT_NE(p7.get(), s7.get());

        // Primary root at v7 has pk, not sk
        EXPECT_TRUE(db_get(db, p7, NibblesView{pk}, 7).has_value());
        EXPECT_FALSE(db_get(db, p7, NibblesView{sk}, 7).has_value());

        // Secondary root at v7 has sk, not pk
        EXPECT_TRUE(db_get(db, s7, NibblesView{sk}, 7).has_value());
        EXPECT_FALSE(db_get(db, s7, NibblesView{pk}, 7).has_value());

        // Both have the shared key from pre-fork (since both were built on
        // top of the primary's pre-fork state... but here secondary started
        // from nullptr, so it only has sk)
        EXPECT_TRUE(db_get(db, p7, NibblesView{shared_key}, 7).has_value());

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Fixture with short history length for GC/compaction tests
    // -------------------------------------------------------------------
    struct DualTimelineShortHistoryFixture : public ::testing::Test
    {
        static constexpr uint64_t SHORT_HISTORY = 20;

        std::filesystem::path const dbname{create_temp_file(8)};
        StateMachineAlwaysMerkle primary_machine;
        StateMachineAlwaysMerkle secondary_machine;
        OnDiskDbConfig config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname},
            .fixed_history_length = SHORT_HISTORY};
        Db db{primary_machine, config};
        std::optional<Db> secondary_db;

        Node::SharedPtr primary_root;
        Node::SharedPtr secondary_root;

        ~DualTimelineShortHistoryFixture()
        {
            std::filesystem::remove(dbname);
        }

        Db &db_for(timeline_id tid)
        {
            if (tid == timeline_id::secondary) {
                MONAD_ASSERT(secondary_db.has_value());
                return *secondary_db;
            }
            return db;
        }

        void activate_secondary(uint64_t fork_version)
        {
            secondary_db.emplace(db.activate_secondary_timeline(
                secondary_machine, fork_version));
        }

        void deactivate_secondary()
        {
            secondary_db.reset();
            db.deactivate_secondary_timeline();
        }

        Node::SharedPtr upsert_kv(
            Node::SharedPtr root, monad::byte_string_view key,
            monad::byte_string_view value, uint64_t version,
            timeline_id tid = timeline_id::primary)
        {
            auto u = make_kv(key, value);
            UpdateList ul;
            ul.push_front(u);
            return db_for(tid).upsert(std::move(root), std::move(ul), version);
        }
    };

    // -------------------------------------------------------------------
    // Test: GC protects secondary's chunks during primary history expiration
    // -------------------------------------------------------------------
    TEST_F(
        DualTimelineShortHistoryFixture,
        gc_protects_secondary_during_primary_history_expiration)
    {
        // Phase 1: Build primary up to SHORT_HISTORY.
        auto const shared_key = 0xAAAAAAAA_bytes;
        for (uint64_t v = 0; v <= SHORT_HISTORY; v++) {
            auto const val = monad::byte_string(4, static_cast<uint8_t>(v));
            primary_root = upsert_kv(primary_root, shared_key, val, v);
        }

        // Phase 2: Activate secondary. Both timelines advance together,
        // exercising the combined GC boundary from the first block onward.
        uint64_t const fork_version = SHORT_HISTORY + 1;
        activate_secondary(fork_version);

        auto const secondary_key = 0xBBBBBBBB_bytes;

        // Phase 3: Drive both timelines well past the history window.
        // Primary's erase_versions_up_to_and_including fires each block,
        // release_unreferenced_chunks must compute the combined-min across
        // both timelines and protect secondary's chunks.
        auto const final_version = fork_version + SHORT_HISTORY * 3;
        for (uint64_t v = fork_version; v <= final_version; v++) {
            auto const pval =
                monad::byte_string(4, static_cast<uint8_t>(v & 0xFF));
            primary_root = upsert_kv(primary_root, shared_key, pval, v);

            auto const sval =
                monad::byte_string(4, static_cast<uint8_t>(v & 0xFF));
            secondary_root = upsert_kv(
                secondary_root, secondary_key, sval, v, timeline_id::secondary);
        }

        // Phase 4: Verify secondary's data survived GC.
        // Use final_version which is within primary's history window.
        auto const sres = db_get(
            db, secondary_root, NibblesView{secondary_key}, final_version);
        ASSERT_TRUE(sres.has_value())
            << "Secondary data lost after primary history expiration";

        // Also verify via load_root_for_version
        auto const loaded_secondary =
            secondary_db->load_root_for_version(final_version);
        ASSERT_NE(loaded_secondary, nullptr)
            << "Secondary root lost after primary history expiration";
        auto const sres2 = db_get(
            db, loaded_secondary, NibblesView{secondary_key}, final_version);
        ASSERT_TRUE(sres2.has_value());

        // Primary's latest data should also be intact
        auto const pres =
            db_get(db, primary_root, NibblesView{shared_key}, final_version);
        ASSERT_TRUE(pres.has_value());

        // Verify timeline isolation: keys are independent
        auto const cross =
            db_get(db, primary_root, NibblesView{secondary_key}, final_version);
        EXPECT_FALSE(cross.has_value());

        deactivate_secondary();
    }

    // -------------------------------------------------------------------
    // Test: Reactivate secondary after deactivation
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, reactivate_after_deactivate)
    {
        // Round 1: activate, upsert, deactivate
        auto const k1 = 0x11111111_bytes;
        primary_root = upsert_kv(primary_root, k1, k1, 0);
        primary_root = upsert_kv(primary_root, k1, k1, 1);

        activate_secondary(0);
        auto const round1_key = 0xAAAAAAAA_bytes;
        secondary_root = upsert_kv(
            secondary_root, round1_key, round1_key, 0, timeline_id::secondary);
        secondary_root = upsert_kv(
            secondary_root, round1_key, round1_key, 1, timeline_id::secondary);

        // Verify round 1 data
        auto const res1 = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{round1_key},
            1);
        ASSERT_TRUE(res1.has_value());

        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));

        // Round 2: reactivate at a later version, upsert new data
        primary_root = upsert_kv(primary_root, k1, k1, 2);
        primary_root = upsert_kv(primary_root, k1, k1, 3);

        activate_secondary(2);
        EXPECT_TRUE(db.timeline_active(timeline_id::secondary));

        auto const round2_key = 0xBBBBBBBB_bytes;
        secondary_root = nullptr; // fresh secondary
        secondary_root = upsert_kv(
            secondary_root, round2_key, round2_key, 2, timeline_id::secondary);
        secondary_root = upsert_kv(
            secondary_root, round2_key, round2_key, 3, timeline_id::secondary);

        // Verify round 2 data
        auto const res2 = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{round2_key},
            3);
        ASSERT_TRUE(res2.has_value());
        EXPECT_EQ(res2.value(), round2_key);

        // Round 1 key should NOT be in round 2 secondary (fresh start)
        auto const res1_in_r2 = db_get(
            db_for(timeline_id::secondary),
            secondary_root,
            NibblesView{round1_key},
            3);
        EXPECT_FALSE(res1_in_r2.has_value());

        // Primary unaffected throughout
        auto const pres = db_get(db, primary_root, NibblesView{k1}, 3);
        ASSERT_TRUE(pres.has_value());

        // Full lifecycle: promote round 2 secondary, then deactivate old
        promote_secondary();
        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));
    }

    // -------------------------------------------------------------------
    // Test: load_root_for_version boundary conditions on secondary
    // -------------------------------------------------------------------
    TEST_F(DualTimelineFixture, load_root_boundary_conditions)
    {
        // Seed primary with versions 0-5
        auto const k1 = 0x11111111_bytes;
        for (uint64_t v = 0; v <= 5; v++) {
            primary_root = upsert_kv(primary_root, k1, k1, v);
        }

        // Activate secondary at version 3, upsert versions 3-5
        activate_secondary(3);
        auto const k2 = 0x22222222_bytes;
        for (uint64_t v = 3; v <= 5; v++) {
            secondary_root =
                upsert_kv(secondary_root, k2, k2, v, timeline_id::secondary);
        }

        // Valid: load secondary at version within range
        auto const loaded = secondary_db->load_root_for_version(4);
        ASSERT_NE(loaded, nullptr);
        auto const res = db_get(*secondary_db, loaded, NibblesView{k2}, 4);
        ASSERT_TRUE(res.has_value());

        // Below fork_version: secondary should return nullptr
        auto const below_fork = secondary_db->load_root_for_version(2);
        EXPECT_EQ(below_fork, nullptr)
            << "load_root_for_version below fork_version should return nullptr";

        // Above max_version: secondary should return nullptr
        auto const above_max = secondary_db->load_root_for_version(6);
        EXPECT_EQ(above_max, nullptr)
            << "load_root_for_version above max_version should return nullptr";

        // After deactivation the secondary Db is gone; verify via
        // timeline_active that the secondary slot is inactive.
        deactivate_secondary();
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));
    }

    // -------------------------------------------------------------------
    // Test: find on secondary root after its version expires from primary
    // -------------------------------------------------------------------
    TEST_F(
        DualTimelineShortHistoryFixture,
        find_on_secondary_after_version_expires_from_primary)
    {
        // Phase 1: Build primary up to the history window.
        auto const shared_key = 0xAAAAAAAA_bytes;
        for (uint64_t v = 0; v <= SHORT_HISTORY; v++) {
            primary_root = upsert_kv(primary_root, shared_key, shared_key, v);
        }

        // Phase 2: Activate secondary and insert secondary-only data.
        uint64_t const fork_version = SHORT_HISTORY + 1;
        activate_secondary(fork_version);

        auto const secondary_key = 0xBBBBBBBB_bytes;
        secondary_root = upsert_kv(
            secondary_root,
            secondary_key,
            secondary_key,
            fork_version,
            timeline_id::secondary);
        // Advance primary at fork_version too
        primary_root =
            upsert_kv(primary_root, shared_key, shared_key, fork_version);

        // Phase 3: Drive primary past the history window so fork_version
        // is erased from the primary ring.
        for (uint64_t v = fork_version + 1;
             v <= fork_version + SHORT_HISTORY + 5;
             v++) {
            primary_root = upsert_kv(primary_root, shared_key, shared_key, v);
        }

        // Sanity: fork_version is no longer in primary's history window
        auto const primary_load = db.load_root_for_version(fork_version);
        EXPECT_EQ(primary_load, nullptr)
            << "fork_version should have been expired from primary";

        // Phase 4: find on the secondary root MUST still work.
        // The secondary root's version (fork_version) is expired from
        // primary but valid in the secondary ring.
        auto const sres = db_get(
            *secondary_db,
            secondary_root,
            NibblesView{secondary_key},
            fork_version);
        ASSERT_TRUE(sres.has_value())
            << "find on secondary root failed after its version expired "
               "from primary";
        EXPECT_EQ(sres.value(), secondary_key);

        // Also verify load_root_for_version still works for secondary
        auto const loaded = secondary_db->load_root_for_version(fork_version);
        ASSERT_NE(loaded, nullptr);
        auto const sres2 = db_get(
            *secondary_db, loaded, NibblesView{secondary_key}, fork_version);
        ASSERT_TRUE(sres2.has_value());
        EXPECT_EQ(sres2.value(), secondary_key);

        deactivate_secondary();
    }

} // namespace
