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

// Profiling harness for snapshot restore. Both cases are DISABLED_ and never
// run in CI; they exist so `perf record` can be pointed at the restore alone,
// with the source db and snapshot built by a separate process.
//
//   B=build/category/execution/ethereum/test
//   MONAD_PROF_DIR=/var/tmp/prof $B/test_restore_profile
//       --gtest_also_run_disabled_tests
//       --gtest_filter=RestoreProfile.DISABLED_BuildAndDump
//   MONAD_PROF_DIR=/var/tmp/prof perf record -g --call-graph=dwarf --
//       $B/test_restore_profile --gtest_also_run_disabled_tests
//       --gtest_filter=RestoreProfile.DISABLED_Load
//
// MONAD_PROF_ACCOUNTS, MONAD_PROF_CONTRACT_EVERY and MONAD_PROF_SLOTS size the
// generated state. MONAD_PROF_CONCURRENCY and MONAD_PROF_PARTITION_MIN_UPDATES
// set the restore's parallel merklization.

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/trie.hpp>

#include <gtest/gtest.h>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>

namespace monad::mpt::test
{
    struct DbAccessor
    {
        static UpdateAux &aux(Db &db)
        {
            return const_cast<UpdateAux &>(db.aux());
        }
    };
}

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint64_t DUMP_BLOCK = 100;

uint64_t env_u64(char const *const name, uint64_t const fallback)
{
    char const *const v = ::getenv(name);
    return v == nullptr ? fallback : std::stoull(v);
}

std::filesystem::path prof_dir()
{
    char const *const v = ::getenv("MONAD_PROF_DIR");
    MONAD_ASSERT_PRINTF(v != nullptr, "MONAD_PROF_DIR is not set");
    return std::filesystem::path{v};
}

MONAD_ANONYMOUS_NAMESPACE_END

TEST(RestoreProfile, DISABLED_BuildAndDump)
{
    using namespace monad;
    using namespace monad::mpt;

    auto const dir = prof_dir();
    std::filesystem::remove_all(dir);
    std::filesystem::create_directories(dir);
    auto const src = (dir / "src.db").string();
    auto const snapshot = (dir / "snapshot").string();
    std::filesystem::create_directories(snapshot);

    uint64_t const accounts = env_u64("MONAD_PROF_ACCOUNTS", 1'000'000);
    uint64_t const contract_every = env_u64("MONAD_PROF_CONTRACT_EVERY", 20);
    uint64_t const slots = env_u64("MONAD_PROF_SLOTS", 20);

    auto const t0 = std::chrono::steady_clock::now();
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src}, .file_size_db = 64}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < DUMP_BLOCK; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(DUMP_BLOCK - 1);

        StateDeltas deltas;
        for (uint64_t i = 0; i < accounts; ++i) {
            StorageDeltas storage;
            if ((i % contract_every) == 0) {
                for (uint64_t j = 0; j < slots; ++j) {
                    storage.emplace(
                        bytes32_t{j + 1},
                        StorageDelta{bytes32_t{}, bytes32_t{i + j + 1}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = std::move(storage)});
        }

        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            deltas,
            Code{},
            bytes32_t{DUMP_BLOCK},
            BlockHeader{.number = DUMP_BLOCK});
        tdb.finalize(DUMP_BLOCK, bytes32_t{DUMP_BLOCK});
        std::cout << "state_root " << to_hex(tdb.state_root()) << std::endl;
    }
    auto const t1 = std::chrono::steady_clock::now();

    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot.c_str(), DUMP_BLOCK);
        char const *const paths[] = {src.c_str()};
        ASSERT_TRUE(monad_db_dump_snapshot(
            paths,
            1,
            static_cast<unsigned>(-1),
            DUMP_BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            /*dump_from_secondary=*/false));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }
    auto const t2 = std::chrono::steady_clock::now();

    using ms = std::chrono::milliseconds;
    std::cout << "accounts " << accounts << "  build "
              << std::chrono::duration_cast<ms>(t1 - t0).count() << " ms  dump "
              << std::chrono::duration_cast<ms>(t2 - t1).count() << " ms"
              << std::endl;
}

TEST(RestoreProfile, DISABLED_Load)
{
    using namespace monad;
    using namespace monad::mpt;

    auto const dir = prof_dir();
    auto const dest = (dir / "dest.db").string();
    auto const snapshot = (dir / "snapshot").string();
    ASSERT_TRUE(std::filesystem::is_directory(snapshot));
    std::filesystem::remove(dest);

    {
        mpt::Db init{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dest}, .file_size_db = 64}};
        monad::mpt::test::DbAccessor::aux(init)
            .metadata_ctx()
            .set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
    }

    auto const concurrency =
        static_cast<unsigned>(env_u64("MONAD_PROF_CONCURRENCY", 0));
    auto const min_updates = static_cast<uint32_t>(
        env_u64("MONAD_PROF_PARTITION_MIN_UPDATES", 1024));
    // 1 keeps the loader serial, so MONAD_PROF_CONCURRENCY alone measures
    // merklization against an unchanged loader.
    auto const load_concurrency =
        static_cast<unsigned>(env_u64("MONAD_PROF_LOAD_CONCURRENCY", 1));

    char const *const paths[] = {dest.c_str()};
    auto const t0 = std::chrono::steady_clock::now();
    monad_db_snapshot_load_filesystem(
        paths,
        1,
        static_cast<unsigned>(-1),
        snapshot.c_str(),
        DUMP_BLOCK,
        /*load_to_secondary=*/false,
        load_concurrency,
        concurrency,
        min_updates);
    auto const t1 = std::chrono::steady_clock::now();

    std::cout << "restore "
              << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0)
                     .count()
              << " ms  concurrency " << concurrency
              << "  partition_min_updates " << min_updates
              << "  load_concurrency " << load_concurrency << std::endl;

    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        tdb.set_block_and_prefix(DUMP_BLOCK);
        std::cout << "state_root " << to_hex(tdb.state_root()) << std::endl;
    }
}
