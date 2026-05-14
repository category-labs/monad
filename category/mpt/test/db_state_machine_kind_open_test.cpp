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

// Verifies that the production-shaped Db ctors (no StateMachine argument)
// route through the kind registry: persisted ring_a/ring_b state_machine_kind
// drives StateMachine construction at open time.

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <optional>
#include <utility>

using namespace monad::mpt;
using namespace monad::test;
using namespace monad::literals;

namespace monad::mpt::test
{
    // Friend-of-Db accessor (db.hpp friends monad::mpt::test::DbAccessor).
    // Each test TU defines its own; tests stay isolated because every test
    // file becomes a standalone gtest binary via add_trie_test.
    struct DbAccessor
    {
        static UpdateAux &aux(Db &db)
        {
            // Db::aux() returns const&; the underlying Impl::aux() is
            // non-const. Tests stamping per-timeline metadata need write
            // access; the const_cast is safe because we never read from a
            // truly-const Db.
            return const_cast<UpdateAux &>(db.aux());
        }
    };
}

namespace
{
    using monad::mpt::test::DbAccessor;

    Update make_kv(monad::byte_string_view key, monad::byte_string_view value)
    {
        return make_update(key, value);
    }

    // Register the ethereum kind to mint a fresh StateMachineAlwaysMerkle
    // every call. Real production registers OnDiskMachine; the test substitutes
    // a trie-compatible test machine so this test stays inside mpt.
    void register_test_state_machines()
    {
        register_state_machine(state_machine_kind::ethereum, [] {
            return std::unique_ptr<StateMachine>(
                new StateMachineAlwaysMerkle{});
        });
    }

    TEST(db_state_machine_kind_open, primary_open_uses_registered_factory)
    {
        std::filesystem::path const dbname = create_temp_file(8);
        auto const unfile = monad::make_scope_exit(
            [&]() noexcept { std::filesystem::remove(dbname); });

        OnDiskDbConfig const create_config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};

        // Stage 1: open with the SM-owning test ctor, stamp the kind on
        // ring_a, then close. Mirrors what monad-mpt --create
        // --state-machine ethereum produces on a fresh pool.
        {
            Db db{std::make_unique<StateMachineAlwaysMerkle>(), create_config};
            DbAccessor::aux(db).metadata_ctx().set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
        }

        // Stage 2: reopen with the production ctor (no SM). The Db ctor
        // must read the kind from db_metadata and instantiate the SM via
        // the registry.
        register_test_state_machines();
        OnDiskDbConfig reopen_config = create_config;
        reopen_config.append = true;
        Db db{reopen_config};

        // Perform a basic upsert + find to confirm the registry-built SM is
        // actually wired into the worker thread.
        auto const k = 0xCAFE_bytes;
        UpdateList ul;
        auto u = make_kv(k, k);
        ul.push_front(u);
        auto const root = db.upsert(nullptr, std::move(ul), 0);
        ASSERT_NE(root, nullptr);
        auto const res = db.find(NodeCursor{root}, NibblesView{k}, 0);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value().node->value(), monad::byte_string_view{k});
    }

    TEST(db_state_machine_kind_open, secondary_open_no_arg_reads_ring_b_kind)
    {
        std::filesystem::path const dbname = create_temp_file(8);
        auto const unfile = monad::make_scope_exit(
            [&]() noexcept { std::filesystem::remove(dbname); });

        OnDiskDbConfig const create_config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};

        // Stage 1: open + activate secondary via the test API, stamp both
        // rings' kinds, then close everything. Mirrors what an operator
        // sees after monad-mpt --create followed by monad-mpt
        // --activate-secondary.
        {
            Db db{std::make_unique<StateMachineAlwaysMerkle>(), create_config};
            DbAccessor::aux(db).metadata_ctx().set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
            auto secondary_db = db.activate_secondary_timeline(
                std::make_unique<StateMachineAlwaysMerkle>());
            DbAccessor::aux(secondary_db)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::secondary, state_machine_kind::ethereum);
        }

        register_test_state_machines();
        OnDiskDbConfig reopen_config = create_config;
        reopen_config.append = true;

        // Stage 2: reopen primary via the production ctor, then attach to
        // the persisted secondary via the no-arg overload.
        Db db{reopen_config};
        auto secondary = db.open_secondary_timeline();
        ASSERT_TRUE(secondary.has_value());
        EXPECT_EQ(secondary->tid(), timeline_id::secondary);

        // Both timelines should be writable + readable through their
        // respective registry-constructed SMs.
        auto const k_primary = 0x1111_bytes;
        auto const k_secondary = 0x2222_bytes;
        UpdateList up;
        auto up_kv = make_kv(k_primary, k_primary);
        up.push_front(up_kv);
        auto const proot = db.upsert(nullptr, std::move(up), 0);
        ASSERT_NE(proot, nullptr);

        UpdateList us;
        auto us_kv = make_kv(k_secondary, k_secondary);
        us.push_front(us_kv);
        auto const sroot = secondary->upsert(nullptr, std::move(us), 0);
        ASSERT_NE(sroot, nullptr);

        auto const pres = db.find(NodeCursor{proot}, NibblesView{k_primary}, 0);
        ASSERT_TRUE(pres.has_value());
        EXPECT_EQ(
            pres.value().node->value(), monad::byte_string_view{k_primary});

        auto const sres =
            secondary->find(NodeCursor{sroot}, NibblesView{k_secondary}, 0);
        ASSERT_TRUE(sres.has_value());
        EXPECT_EQ(
            sres.value().node->value(), monad::byte_string_view{k_secondary});
    }

    TEST(db_state_machine_kind_open, secondary_open_inactive_returns_nullopt)
    {
        std::filesystem::path const dbname = create_temp_file(8);
        auto const unfile = monad::make_scope_exit(
            [&]() noexcept { std::filesystem::remove(dbname); });

        OnDiskDbConfig const create_config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};

        {
            Db db{std::make_unique<StateMachineAlwaysMerkle>(), create_config};
            DbAccessor::aux(db).metadata_ctx().set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
        }

        register_test_state_machines();
        OnDiskDbConfig reopen_config = create_config;
        reopen_config.append = true;
        Db db{reopen_config};
        EXPECT_FALSE(db.open_secondary_timeline().has_value());
    }
}
