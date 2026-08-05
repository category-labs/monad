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

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.h>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>

#include <test_resource_data.h>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <vector>

namespace monad::mpt::test
{
    // Friend-of-Db accessor (db.hpp friends monad::mpt::test::DbAccessor).
    // Lets tests stamp the persisted state_machine_kind on a freshly-
    // truncated pool before the snapshot loader (which uses the
    // metadata-driven Db ctor internally) reads from it.
    struct DbAccessor
    {
        static UpdateAux &aux(Db &db)
        {
            return const_cast<UpdateAux &>(db.aux());
        }
    };
}

namespace
{
    struct TempDb
    {
        int fd;
        std::string path;

        explicit TempDb(uint64_t const bytes = 8ULL * 1024 * 1024 * 1024)
            : fd{MONAD_ASYNC_NAMESPACE::make_temporary_inode()}
            , path{"/proc/self/fd/" + std::to_string(fd)}
        {
            MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(bytes)));
        }

        TempDb(TempDb const &) = delete;
        TempDb &operator=(TempDb const &) = delete;

        ~TempDb()
        {
            ::close(fd);
        }
    };

    struct TempDir
    {
        std::filesystem::path path;

        TempDir()
        {
            std::filesystem::path tmpl =
                MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                "monad_snapshot_test_XXXXXX";
            char *const result = ::mkdtemp((char *)tmpl.native().data());
            MONAD_ASSERT(result != nullptr);
            path = result;
        }

        TempDir(TempDir const &) = delete;
        TempDir &operator=(TempDir const &) = delete;

        ~TempDir()
        {
            std::error_code ec;
            std::filesystem::remove_all(path, ec);
        }
    };

    // Recomputes, from the offsets actually recorded in each node's fnext
    // array, the minimum virtual offset over every subtrie, and compares it
    // against the min-offset pair the writer stored in the parent. Compaction
    // prunes its walk with those stored pairs, so an entry that is not the true
    // minimum silently leaves data below the compaction boundary unrewritten.
    struct MinOffsetVerifier final : public monad::mpt::TraverseMachine
    {
        monad::mpt::UpdateAux const *aux{nullptr};
        size_t nodes{0};
        size_t compared{0};

        struct Record
        {
            monad::mpt::Node const *node{nullptr};
            monad::mpt::compact_offset_pair subtrie_min{};
        };

        std::vector<Record> path;

        bool
        down(unsigned char const branch, monad::mpt::Node const &node) override
        {
            ++nodes;
            monad::mpt::compact_offset_pair own;
            if (!path.empty()) {
                auto const *parent = path.back().node;
                auto const virt = aux->physical_to_virtual(
                    parent->fnext(parent->to_child_index(branch)));
                MONAD_ASSERT(virt != monad::mpt::INVALID_VIRTUAL_OFFSET);
                (virt.in_fast_list() ? own.fast : own.slow) =
                    monad::mpt::compact_virtual_chunk_offset_t{virt};
            }
            path.push_back({&node, own});
            return true;
        }

        void up(unsigned char const branch, monad::mpt::Node const &) override
        {
            auto const child = path.back();
            path.pop_back();
            if (path.empty()) {
                return;
            }
            auto &parent = path.back();
            auto const stored =
                parent.node->min_offsets(parent.node->to_child_index(branch));
            EXPECT_EQ((uint32_t)stored.fast, (uint32_t)child.subtrie_min.fast)
                << "min_offset_fast at node " << nodes << " branch "
                << static_cast<unsigned>(branch);
            EXPECT_EQ((uint32_t)stored.slow, (uint32_t)child.subtrie_min.slow)
                << "min_offset_slow at node " << nodes << " branch "
                << static_cast<unsigned>(branch);
            ++compared;
            parent.subtrie_min.fast =
                std::min(parent.subtrie_min.fast, child.subtrie_min.fast);
            parent.subtrie_min.slow =
                std::min(parent.subtrie_min.slow, child.subtrie_min.slow);
        }

        std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<MinOffsetVerifier>(*this);
        }
    };

    // Slot-encoded source db holding `accounts` accounts, each with its own
    // index as balance and nonce, and every fiftieth one also holding slots
    // 0..9 valued by index. Slot 0 is written as zero, which is a deletion, so
    // only slots 1..9 survive. Returns the state root at `block`.
    monad::bytes32_t build_source_db(
        TempDb const &src, uint64_t const accounts, uint64_t const block)
    {
        using namespace monad;
        using namespace monad::mpt;

        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src.path}}};
        load_header({}, db, BlockHeader{.number = 0});
        db.update_finalized_version(0);
        StateDeltas deltas;
        for (uint64_t i = 0; i < accounts; ++i) {
            StorageDeltas storage;
            if ((i % 50) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    storage.emplace(
                        bytes32_t{j}, StorageDelta{bytes32_t{}, bytes32_t{j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = storage});
        }
        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            deltas,
            Code{},
            bytes32_t{block},
            BlockHeader{.number = block});
        tdb.finalize(block, bytes32_t{block});
        return tdb.state_root();
    }

    // Single-shard dump of `block` from the primary timeline of `src`.
    void
    dump_snapshot(TempDb const &src, TempDir const &dir, uint64_t const block)
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                dir.path.c_str(), block);
        char const *dbpath[] = {src.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbpath,
            1,
            static_cast<unsigned>(-1),
            block,
            monad_db_snapshot_write_filesystem,
            context,
            /*dump_concurrency_limit=*/2048,
            /*total_shards=*/1,
            /*shard_number=*/0,
            /*dump_from_secondary=*/false));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }

    // Stamp the kind so the snapshot loader's metadata-driven Db ctor (via
    // monad_db_snapshot_loader_create) can resolve it. This is also the only
    // open that creates the storage pool, so it is the only one where
    // chunk_capacity takes effect.
    void init_dest(
        TempDb const &dest, monad::mpt::state_machine_kind const kind,
        uint32_t const chunk_capacity_bits =
            monad::mpt::OnDiskDbConfig{}.chunk_capacity)
    {
        using namespace monad;
        using namespace monad::mpt;

        mpt::Db dest_init{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{
                .dbname_paths = {dest.path},
                .chunk_capacity = chunk_capacity_bits}};
        monad::mpt::test::DbAccessor::aux(dest_init)
            .metadata_ctx()
            .set_state_machine_kind(timeline_id::primary, kind);
    }

    // Reads back what build_source_db wrote, for account indices below
    // `accounts`. A root hash does not depend on child offsets, so it cannot
    // tell a correctly written subtrie from an unreachable one; only reading
    // the leaves can.
    void expect_entries_readable(monad::TrieDb &tdb, uint64_t const accounts)
    {
        using namespace monad;

        Incarnation const inc{0, 0};
        for (uint64_t i = 0; i < accounts; i += 50) {
            Address const addr{i};
            auto const account = tdb.read_account(addr);
            EXPECT_TRUE(account.has_value()) << "account " << i;
            if (account.has_value()) {
                EXPECT_EQ(account->balance, i);
            }
            for (uint64_t j = 1; j < 10; ++j) {
                EXPECT_EQ(
                    tdb.read_storage(addr, inc, bytes32_t{j}), bytes32_t{j})
                    << "account " << i << " slot " << j;
            }
        }
    }
}

TEST(DbBinarySnapshot, Basic)
{
    using namespace monad;
    using namespace monad::mpt;

    TempDb const src_db;
    TempDb const dest_db;
    TempDir const snapshot_dir;

    bytes32_t root_hash;
    Code code_delta;
    BlockHeader last_header;
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < 100; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        for (uint64_t i = 0; i < 100'000; ++i) {
            StorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    storage.emplace(
                        bytes32_t{j}, StorageDelta{bytes32_t{}, bytes32_t{j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = storage});
        }
        for (uint64_t i = 0; i < 1'000; ++i) {
            std::vector<uint64_t> const bytes(100, i);
            byte_string_view const code{
                reinterpret_cast<unsigned char const *>(bytes.data()),
                bytes.size() * sizeof(uint64_t)};
            bytes32_t const hash = to_bytes(keccak256(code));
            auto const icode = vm::make_shared_intercode(code);
            code_delta.emplace(hash, icode);
        }
        TrieDb tdb{db};
        ASSERT_EQ(tdb.get_block_number(), db.get_latest_version());
        monad::test::commit_simple(
            tdb,
            StateDeltas(std::move(deltas)),
            code_delta,
            bytes32_t{100},
            BlockHeader{.number = 100});
        tdb.finalize(100, bytes32_t{100});
        last_header = tdb.read_eth_header();
        root_hash = tdb.state_root();
    }

    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), 100);
        char const *dbname_paths[] = {src_db.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            100,
            monad_db_snapshot_write_filesystem,
            context,
            2048, // dump_concurrency_limit
            1, // total_shards
            0, // shard_number
            /*dump_from_secondary=*/false));

        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        {
            mpt::Db dest_init{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
            // Stamp the kind so the snapshot loader's metadata-driven
            // Db ctor (via monad_db_snapshot_loader_create) can resolve
            // it.
            monad::mpt::test::DbAccessor::aux(dest_init)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::primary, state_machine_kind::ethereum);
        }
        char const *dbname_paths_new[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            100,
            /*load_to_secondary=*/false,
            /*load_concurrency=*/1u,
            /*upsert_concurrency=*/0,
            /*partition_min_updates=*/0);
    }

    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.set_block_and_prefix(i);
            EXPECT_EQ(tdb.read_eth_header(), BlockHeader{.number = i});
        }
        tdb.set_block_and_prefix(100);
        EXPECT_EQ(tdb.read_eth_header(), last_header);
        EXPECT_EQ(tdb.state_root(), root_hash);
        for (auto const &[hash, icode] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(
                byte_string_view(from_db->code(), from_db->size()),
                byte_string_view(icode->code(), icode->size()));
        }
    }
}

// Merklizing the restored trie across worker threads must not change it. Both
// target encodings are covered because they hash storage with different
// Compute objects, and those carry state across calls.
TEST(DbBinarySnapshot, ParallelMerklizationMatchesSerial)
{
    using namespace monad;
    using namespace monad::mpt;

    constexpr uint64_t BLOCK = 1;
    constexpr unsigned WORKERS = 8;
    // The loader flushes per shard, so one upsert here carries only a few
    // hundred accounts and its sublists are a dozen or so entries. A
    // mainnet-scale threshold would leave nothing partitioned and the test
    // would quietly stop covering the parallel path.
    constexpr uint32_t PARTITION_MIN_UPDATES = 4;
    constexpr uint64_t ACCOUNTS = 50'000;
    // Read-back is a spot check here: ParallelLoadMatchesSerialSlot and
    // CompactionAfterParallelRestore cover the whole key space.
    constexpr uint64_t ACCOUNTS_TO_READ_BACK = 1'000;

    TempDb const src_db;
    TempDir const snapshot_dir;

    bytes32_t const source_root = build_source_db(src_db, ACCOUNTS, BLOCK);
    dump_snapshot(src_db, snapshot_dir, BLOCK);

    auto const restored_root = [&snapshot_dir, BLOCK](
                                   TempDb const &dest,
                                   state_machine_kind const kind,
                                   unsigned const concurrency) {
        init_dest(dest, kind);
        char const *dbpath[] = {dest.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dbpath,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/false,
            /*load_concurrency=*/1u,
            concurrency,
            PARTITION_MIN_UPDATES);

        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest.path}}};
        mpt::Db db{io_context};
        EXPECT_EQ(db.get_latest_version(), BLOCK);
        TrieDb tdb{db};
        tdb.set_block_and_prefix(BLOCK);
        expect_entries_readable(tdb, ACCOUNTS_TO_READ_BACK);
        return tdb.state_root();
    };

    TempDb const slot_serial;
    TempDb const slot_parallel;
    TempDb const page_serial;
    TempDb const page_parallel;

    EXPECT_EQ(
        restored_root(slot_serial, state_machine_kind::ethereum, 0),
        source_root);
    EXPECT_EQ(
        restored_root(slot_parallel, state_machine_kind::ethereum, WORKERS),
        source_root);

    // Page and slot encodings hash to different roots by design, so the page
    // target is compared against its own serial load.
    auto const page_root =
        restored_root(page_serial, state_machine_kind::monad, 0);
    EXPECT_NE(page_root, source_root);
    EXPECT_EQ(
        restored_root(page_parallel, state_machine_kind::monad, WORKERS),
        page_root);
}

// Compaction decides whether to rewrite a subtrie by reading the min-offset
// arrays that the restore wrote into every parent, so it -- not the root hash,
// which is independent of child offsets -- is where an offset a worker got
// wrong surfaces.
TEST(DbBinarySnapshot, CompactionAfterParallelRestore)
{
    using namespace monad;
    using namespace monad::mpt;

    constexpr uint64_t BLOCK = 1;
    constexpr unsigned WORKERS = 4;
    constexpr uint32_t PARTITION_MIN_UPDATES = 4;
    // Versions upserted with compaction on. Each advances the slow-list
    // compaction boundary by one compact_virtual_chunk_offset_t unit (64 KiB).
    constexpr uint64_t COMPACTION_VERSIONS = 8;
    // The loader upserts with can_write_to_fast = false, so the restored trie
    // lands in the slow list, and UpdateAux::advance_compact_offsets only
    // starts compacting that list once total pool usage exceeds 60% and
    // slow-list usage exceeds 20%. The destination pool is therefore sized so
    // that the restore alone clears both: 8 MiB chunks (the smallest AsyncIO
    // accepts) and few enough of them. The usage assertions below fail loudly
    // if a change in node footprint moves it out of that window, rather than
    // letting the test silently stop compacting.
    constexpr uint32_t DEST_CHUNK_CAPACITY_BITS = 23;
    constexpr uint64_t DEST_POOL_BYTES = 58ULL << 20;
    // Sized so the restored trie lands near the middle of its second 8 MiB
    // slow chunk, which is what leaves the usage window above room to drift.
    constexpr uint64_t ACCOUNTS = 65'000;

    TempDb const src_db;
    TempDir const snapshot_dir;

    bytes32_t const source_root = build_source_db(src_db, ACCOUNTS, BLOCK);
    dump_snapshot(src_db, snapshot_dir, BLOCK);

    TempDb const dest_db{DEST_POOL_BYTES};
    init_dest(dest_db, state_machine_kind::ethereum, DEST_CHUNK_CAPACITY_BITS);
    char const *dest_paths[] = {dest_db.path.c_str()};
    monad_db_snapshot_load_filesystem(
        dest_paths,
        1,
        static_cast<unsigned>(-1),
        snapshot_dir.path.c_str(),
        BLOCK,
        /*load_to_secondary=*/false,
        /*load_concurrency=*/1u,
        WORKERS,
        PARTITION_MIN_UPDATES);

    compact_offset_pair boundary_before{};
    compact_offset_pair boundary_after{};
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{
                .append = true,
                .compaction = true,
                .dbname_paths = {dest_db.path},
                .chunk_capacity = DEST_CHUNK_CAPACITY_BITS}};
        auto &aux = monad::mpt::test::DbAccessor::aux(db);
        double const slow_usage = aux.num_chunks(UpdateAux::chunk_list::slow) /
                                  static_cast<double>(aux.io->chunk_count());
        ASSERT_GT(aux.disk_usage(), 0.6)
            << "destination pool no longer full enough for slow-list "
               "compaction to start; retune ACCOUNTS or DEST_POOL_BYTES";
        ASSERT_GT(slow_usage, 0.2)
            << "restore no longer fills enough of the slow list; retune "
               "ACCOUNTS or DEST_POOL_BYTES";
        ASSERT_LT(aux.disk_usage(), 0.8)
            << "destination pool too full: history trimming would run and the "
               "compaction upserts may run out of chunks; retune ACCOUNTS or "
               "DEST_POOL_BYTES";

        // Compaction prunes its walk with the min-offset pair each parent
        // stores per child, so every one of them has to be the true minimum
        // over that child's subtrie.
        auto verify_min_offsets = [&](uint64_t const version) {
            auto const root = db.load_root_for_version(version);
            MONAD_ASSERT(root);
            MinOffsetVerifier verifier;
            verifier.aux = &aux;
            EXPECT_TRUE(
                db.traverse_blocking(NodeCursor{root}, verifier, version));
            EXPECT_TRUE(verifier.path.empty());
            EXPECT_GT(verifier.compared, 10'000u)
                << "traversal covered too little of the restored trie";
            return compact_offset_pair::deserialize(root->value());
        };

        boundary_before = verify_min_offsets(BLOCK);
        TrieDb tdb{db};
        tdb.set_block_and_prefix(BLOCK);
        // Compaction only descends where the update itself descends, so these
        // have to touch the state table rather than the block header alone.
        for (uint64_t v = BLOCK + 1; v <= BLOCK + COMPACTION_VERSIONS; ++v) {
            StateDeltas deltas;
            deltas.emplace(
                Address{1'000'000 + v},
                StateDelta{
                    .account = {std::nullopt, Account{.balance = v}},
                    .storage = {}});
            monad::test::commit_simple(
                tdb, deltas, Code{}, bytes32_t{v}, BlockHeader{.number = v});
            tdb.finalize(v, bytes32_t{v});
        }
        boundary_after = verify_min_offsets(BLOCK + COMPACTION_VERSIONS);
    }

    /* A moved boundary shows compaction ran over the restored region and pruned
    self-consistently: advance_compact_offsets aborts if the trie still
    references an offset below the boundary it recorded last version. It does
    not show the recorded minima are the true ones, because that same function
    derives the boundary from the minimum it later checks against
    (update_aux.cpp:904-913), so a uniformly too-high minimum passes here. Only
    MinOffsetVerifier catches that, which is why both checks exist. */
    EXPECT_GT((uint32_t)boundary_after.slow, (uint32_t)boundary_before.slow);

    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        EXPECT_EQ(db.get_latest_version(), BLOCK + COMPACTION_VERSIONS);
        TrieDb tdb{db};
        // The restored version is still readable, and still hashes to what the
        // source did, after compaction rewrote part of it.
        tdb.set_block_and_prefix(BLOCK);
        EXPECT_EQ(tdb.state_root(), source_root);
        tdb.set_block_and_prefix(BLOCK + COMPACTION_VERSIONS);
        expect_entries_readable(tdb, ACCOUNTS);
    }
}

TEST(DbBinarySnapshot, MultipleShards)
{
    using namespace monad;
    using namespace monad::mpt;

    TempDb const src_db;
    TempDb const dest_db;
    TempDir const base_root;
    TempDir const combined_root;

    bytes32_t root_hash;
    Code code_delta;
    BlockHeader last_header;
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < 100; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        for (uint64_t i = 0; i < 100'000; ++i) {
            StorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    storage.emplace(
                        bytes32_t{j}, StorageDelta{bytes32_t{}, bytes32_t{j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = storage});
        }
        for (uint64_t i = 0; i < 1'000; ++i) {
            std::vector<uint64_t> const bytes(100, i);
            byte_string_view const code{
                reinterpret_cast<unsigned char const *>(bytes.data()),
                bytes.size() * sizeof(uint64_t)};
            bytes32_t const hash = to_bytes(keccak256(code));
            auto const icode = vm::make_shared_intercode(code);
            code_delta.emplace(hash, icode);
        }
        TrieDb tdb{db};
        ASSERT_EQ(tdb.get_block_number(), db.get_latest_version());
        monad::test::commit_simple(
            tdb,
            StateDeltas(std::move(deltas)),
            code_delta,
            bytes32_t{100},
            BlockHeader{.number = 100});
        tdb.finalize(100, bytes32_t{100});
        last_header = tdb.read_eth_header();
        root_hash = tdb.state_root();
    }

    {
        constexpr uint64_t NUM_SHARDS = 4;

        std::vector<std::filesystem::path> shard_roots;
        for (uint64_t shard = 0; shard < NUM_SHARDS; ++shard) {
            auto const shard_root =
                base_root.path / ("shard_" + std::to_string(shard));
            shard_roots.push_back(shard_root);

            auto *const context =
                monad_db_snapshot_filesystem_write_user_context_create(
                    shard_root.c_str(), 100);
            char const *dbname_paths[] = {src_db.path.c_str()};
            EXPECT_TRUE(monad_db_dump_snapshot(
                dbname_paths,
                1,
                static_cast<unsigned>(-1),
                100,
                monad_db_snapshot_write_filesystem,
                context,
                2048, // dump_concurrency_limit
                NUM_SHARDS,
                shard,
                /*dump_from_secondary=*/false));

            monad_db_snapshot_filesystem_write_user_context_destroy(context);
        }

        auto const combined_version_dir = combined_root.path / "100";
        std::filesystem::create_directories(combined_version_dir);

        uint64_t total_shards_copied = 0;
        for (uint64_t shard = 0; shard < NUM_SHARDS; ++shard) {
            auto const src_dir = shard_roots[shard] / "100";
            if (!std::filesystem::exists(src_dir)) {
                continue;
            }

            for (auto const &entry :
                 std::filesystem::directory_iterator(src_dir)) {
                if (entry.is_directory()) {
                    auto const shard_name = entry.path().filename();
                    auto const dest_shard_dir =
                        combined_version_dir / shard_name;

                    if (!std::filesystem::exists(dest_shard_dir)) {
                        std::filesystem::copy(
                            entry.path(),
                            dest_shard_dir,
                            std::filesystem::copy_options::recursive);
                        ++total_shards_copied;
                    }
                }
            }
        }

        EXPECT_EQ(total_shards_copied, 256u);
        {
            mpt::Db dest_init{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
            // Stamp the kind so the snapshot loader's metadata-driven
            // Db ctor (via monad_db_snapshot_loader_create) can resolve
            // it.
            monad::mpt::test::DbAccessor::aux(dest_init)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::primary, state_machine_kind::ethereum);
        }
        char const *dbname_paths_new[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new,
            1,
            static_cast<unsigned>(-1),
            combined_root.path.c_str(),
            100,
            /*load_to_secondary=*/false,
            /*load_concurrency=*/1u,
            /*upsert_concurrency=*/0,
            /*partition_min_updates=*/0);
    }
    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.set_block_and_prefix(i);
            EXPECT_EQ(tdb.read_eth_header(), BlockHeader{.number = i});
        }
        tdb.set_block_and_prefix(100);
        EXPECT_EQ(tdb.read_eth_header(), last_header);
        EXPECT_EQ(tdb.state_root(), root_hash);
        for (auto const &[hash, icode] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(
                byte_string_view(from_db->code(), from_db->size()),
                byte_string_view(icode->code(), icode->size()));
        }
    }
}

namespace
{
    // Counts only storage leaves (entries nested under an account) under the
    // cursor passed to Db::traverse. The cursor is expected to point at the
    // state subtree root, so the path depth from there is:
    //   account leaf at 64 nibbles (keccak256 addr)
    //   storage leaf at 128 nibbles (account keccak + storage-key keccak)
    // Anything shallower (the state-marker node, intermediate branches,
    // account leaves) is skipped.
    struct LeafCounter final : public monad::mpt::TraverseMachine
    {
        static constexpr uint8_t STORAGE_LEAF_DEPTH =
            static_cast<uint8_t>(KECCAK256_SIZE * 2 * 2);
        size_t count{0};
        uint8_t depth{0};

        bool
        down(unsigned char const branch, monad::mpt::Node const &node) override
        {
            if (branch == monad::mpt::INVALID_BRANCH) {
                return true;
            }
            depth = static_cast<uint8_t>(depth + 1 + node.path_nibbles_len());
            if (depth == STORAGE_LEAF_DEPTH && node.has_value()) {
                ++count;
            }
            return true;
        }

        void
        up(unsigned char const branch, monad::mpt::Node const &node) override
        {
            if (branch == monad::mpt::INVALID_BRANCH) {
                return;
            }
            depth = static_cast<uint8_t>(depth - 1 - node.path_nibbles_len());
        }

        std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<LeafCounter>(*this);
        }
    };
}

TEST(DbBinarySnapshot, LoadPageModeOnSecondaryDb)
{
    using namespace monad;
    using namespace monad::mpt;

    // Slots 0x00, 0x01, 0x7f share page_key 0; slots 0x80, 0x81 share page_key
    // 1. With storage_page_t::SLOTS == 128, this exercises both grouping
    // (multiple slots on one page) and separation (slots split across pages).
    constexpr uint64_t BLOCK = 1;
    constexpr std::array<uint8_t, 5> SLOT_BYTES{0x00, 0x01, 0x7f, 0x80, 0x81};
    std::array<Address, 2> const ADDRS{Address{1}, Address{2}};

    auto make_slot = [](uint8_t b) {
        bytes32_t k{};
        k.bytes[31] = b;
        return k;
    };
    auto make_val = [](Address const &a, uint8_t b) {
        bytes32_t v{};
        v.bytes[30] = a.bytes[19];
        v.bytes[31] = static_cast<uint8_t>(b ^ 0xa5);
        return v;
    };

    ASSERT_EQ(compute_page_key(make_slot(0x00)), bytes32_t{});
    ASSERT_EQ(compute_page_key(make_slot(0x01)), bytes32_t{});
    ASSERT_EQ(compute_page_key(make_slot(0x7f)), bytes32_t{});
    ASSERT_EQ(compute_page_key(make_slot(0x80)), make_slot(0x01));
    ASSERT_EQ(compute_page_key(make_slot(0x81)), make_slot(0x01));

    TempDb const dbname;
    TempDir const snapshot_dir;

    // Build slot-encoded source db with two accounts.
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dbname.path}}};
        load_header({}, db, BlockHeader{.number = 0});
        db.update_finalized_version(0);
        StateDeltas deltas;
        for (auto const &addr : ADDRS) {
            StorageDeltas storage;
            for (auto const b : SLOT_BYTES) {
                storage.emplace(
                    make_slot(b), StorageDelta{bytes32_t{}, make_val(addr, b)});
            }
            deltas.emplace(
                addr,
                StateDelta{
                    .account = {std::nullopt, Account{.balance = 1}},
                    .storage = storage});
        }
        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            deltas,
            Code{},
            bytes32_t{BLOCK},
            BlockHeader{.number = BLOCK});
        tdb.finalize(BLOCK, bytes32_t{BLOCK});
    }

    // Dump slot-encoded snapshot, then load it into a page-encoded secondary.
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), BLOCK);
        char const *dbpath[] = {dbname.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbpath,
            1,
            static_cast<unsigned>(-1),
            BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            /*dump_from_secondary=*/false));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        // The loader opens (does not activate) the secondary, so activate it
        // and stamp its kind (= monad) up front. Both handles are destroyed
        // before the load so the loader holds the only timeline references.
        {
            mpt::Db primary{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.append = true, .dbname_paths = {dbname.path}}};
            [[maybe_unused]] auto const secondary =
                primary.activate_secondary_timeline(
                    std::make_unique<monad::MonadOnDiskMachine>());
            MONAD_ASSERT(primary.timeline_active(timeline_id::secondary));
        }

        // Target encoding is derived from the secondary's stamped kind, so
        // the slot snapshot is converted to page leaves on the fly.
        monad_db_snapshot_load_filesystem(
            dbpath,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/true,
            /*load_concurrency=*/1u,
            /*upsert_concurrency=*/0,
            /*partition_min_updates=*/0);
    }

    // Verify secondary db is page-encoded and round-trip slot reads match.
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {dbname.path}}};
        {
            auto db2 = db.open_secondary_timeline(
                std::make_unique<monad::MonadOnDiskMachine>());
            ASSERT_TRUE(db2.has_value());
            db = std::move(db2.value());
        }
        TrieDb tdb{db};
        ASSERT_TRUE(tdb.is_page_encoded());
        tdb.set_block_and_prefix(BLOCK);
        Incarnation const inc{0, 0};

        for (auto const &addr : ADDRS) {
            ASSERT_TRUE(tdb.read_account(addr).has_value());
            for (auto const b : SLOT_BYTES) {
                EXPECT_EQ(
                    tdb.read_storage(addr, inc, make_slot(b)),
                    make_val(addr, b))
                    << "addr=" << static_cast<int>(addr.bytes[19]) << " slot=0x"
                    << std::hex << static_cast<int>(b);
            }

            auto const page0 = tdb.read_storage_page(addr, inc, bytes32_t{});
            EXPECT_EQ(page0[0], make_val(addr, 0x00));
            EXPECT_EQ(page0[1], make_val(addr, 0x01));
            EXPECT_EQ(page0[0x7f], make_val(addr, 0x7f));
            for (size_t i = 2; i < 0x7f; ++i) {
                EXPECT_EQ(page0[static_cast<uint8_t>(i)], bytes32_t{});
            }

            bytes32_t const pk1 = compute_page_key(make_slot(0x80));
            auto const page1 = tdb.read_storage_page(addr, inc, pk1);
            EXPECT_EQ(page1[0], make_val(addr, 0x80));
            EXPECT_EQ(page1[1], make_val(addr, 0x81));
            for (size_t i = 2; i < storage_page_t::SLOTS; ++i) {
                EXPECT_EQ(page1[static_cast<uint8_t>(i)], bytes32_t{});
            }

            // Read raw leaves by hash path and decode the page.
            auto const account_path = concat(
                finalized_nibbles,
                STATE_NIBBLE,
                NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})});
            for (bytes32_t const &page_key : {bytes32_t{}, pk1}) {
                auto const leaf_res = db.find(
                    concat(
                        NibblesView{account_path},
                        NibblesView{keccak256(
                            {page_key.bytes, sizeof(page_key.bytes)})}),
                    BLOCK);
                ASSERT_TRUE(leaf_res.has_value());
                auto enc = leaf_res.value().node->value();
                auto const inner = decode_storage_db_ignore_key(enc);
                ASSERT_TRUE(inner.has_value());
                auto const decoded = decode_storage_page(inner.value());
                ASSERT_TRUE(decoded.has_value());
                EXPECT_EQ(
                    decoded.value(),
                    tdb.read_storage_page(addr, inc, page_key));
            }
        }

        // Confirm slot grouping happened during load: each account holds
        // exactly two storage pages (page_key 0 and page_key 1), so the
        // state subtree should hold ADDRS.size() * 2 storage leaves total
        // (the source had ADDRS.size() * 5 = 10 slot leaves before grouping).
        auto const state_cursor =
            db.find(concat(finalized_nibbles, STATE_NIBBLE), BLOCK);
        ASSERT_TRUE(state_cursor.has_value());
        ASSERT_TRUE(state_cursor.value().is_valid());
        LeafCounter counter;
        ASSERT_TRUE(db.traverse_blocking(state_cursor.value(), counter, BLOCK));
        EXPECT_EQ(counter.count, ADDRS.size() * 2);
    }
}

// Dump from a page-encoded secondary timeline, then load into a fresh
// slot-encoded primary db. This is the dual-db migration path: the secondary
// holds page-encoded state, monad_db_dump_snapshot(dump_from_secondary=true)
// expands each page leaf into slot-format entries, and the resulting slot
// snapshot restores into a standalone slot db. Reverse of
// LoadPageModeOnSecondaryDb.
TEST(DbBinarySnapshot, DumpFromSecondaryPageDb)
{
    using namespace monad;
    using namespace monad::mpt;

    // Slots 0x00, 0x01, 0x7f share page_key 0; slots 0x80, 0x81 share page_key
    // 1, so the source spans two pages per account.
    constexpr uint64_t BLOCK = 1;
    constexpr std::array<uint8_t, 5> SLOT_BYTES{0x00, 0x01, 0x7f, 0x80, 0x81};
    std::array<Address, 2> const ADDRS{Address{1}, Address{2}};

    auto make_slot = [](uint8_t b) {
        bytes32_t k{};
        k.bytes[31] = b;
        return k;
    };
    auto make_val = [](Address const &a, uint8_t b) {
        bytes32_t v{};
        v.bytes[30] = a.bytes[19];
        v.bytes[31] = static_cast<uint8_t>(b ^ 0xa5);
        return v;
    };

    TempDb const src_db;
    TempDb const dest_db;
    TempDir const snapshot_dir;

    // Build a slot-encoded primary with a page-encoded secondary, and populate
    // the secondary (MonadOnDiskMachine stamps its kind = monad).
    {
        mpt::Db db1{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        // Activate before any TrieDb exists (requires worker_thread_use_count
        // == 1). db2 is bound to the secondary timeline.
        mpt::Db db2 = db1.activate_secondary_timeline(
            std::make_unique<monad::MonadOnDiskMachine>());
        load_header({}, db2, BlockHeader{.number = 0});
        db2.update_finalized_version(0);
        StateDeltas deltas;
        for (auto const &addr : ADDRS) {
            StorageDeltas storage;
            for (auto const b : SLOT_BYTES) {
                storage.emplace(
                    make_slot(b), StorageDelta{bytes32_t{}, make_val(addr, b)});
            }
            deltas.emplace(
                addr,
                StateDelta{
                    .account = {std::nullopt, Account{.balance = 1}},
                    .storage = storage});
        }
        TrieDb tdb2{db2};
        ASSERT_TRUE(tdb2.is_page_encoded());
        // A page-encoded db must commit through PageCommitBuilder (TrieDb
        // asserts the builder type matches the encoding).
        PageCommitBuilder builder(BLOCK, tdb2);
        builder.add_state_deltas(deltas).add_code(Code{});
        BlockHeader const header{.number = BLOCK};
        tdb2.commit(
            bytes32_t{BLOCK}, builder, header, deltas, [&](BlockHeader &h) {
                h.receipts_root = tdb2.receipts_root();
                h.state_root = tdb2.state_root();
                h.withdrawals_root = tdb2.withdrawals_root();
                h.transactions_root = tdb2.transactions_root();
            });
        tdb2.finalize(BLOCK, bytes32_t{BLOCK});
    }

    // Dump from the secondary (expands page leaves to slot entries), then load
    // into a fresh slot-encoded primary.
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), BLOCK);
        char const *srcpath[] = {src_db.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            srcpath,
            1,
            static_cast<unsigned>(-1),
            BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            /*dump_from_secondary=*/true));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        {
            mpt::Db dest_init{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
            monad::mpt::test::DbAccessor::aux(dest_init)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::primary, state_machine_kind::ethereum);
        }
        char const *dest_path[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dest_path,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/false,
            /*load_concurrency=*/1u,
            /*upsert_concurrency=*/0,
            /*partition_min_updates=*/0);
    }

    // Verify the target is slot-encoded and every slot round-trips.
    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        ASSERT_FALSE(tdb.is_page_encoded());
        tdb.set_block_and_prefix(BLOCK);
        Incarnation const inc{0, 0};
        for (auto const &addr : ADDRS) {
            ASSERT_TRUE(tdb.read_account(addr).has_value());
            for (auto const b : SLOT_BYTES) {
                EXPECT_EQ(
                    tdb.read_storage(addr, inc, make_slot(b)),
                    make_val(addr, b))
                    << "addr=" << static_cast<int>(addr.bytes[19]) << " slot=0x"
                    << std::hex << static_cast<int>(b);
            }
        }
    }
}

// A parallel load (concurrency = 0 => all cores) must produce a bit-identical
// state root to a serial load (concurrency = 1) and to the source db, since the
// 256 shards are disjoint subtrees committed into one version.
TEST(DbBinarySnapshot, ParallelLoadMatchesSerialSlot)
{
    using namespace monad;
    using namespace monad::mpt;

    constexpr uint64_t BLOCK = 100;
    TempDb const src_db;
    TempDir const snapshot_dir;

    bytes32_t root_hash;
    Code code_delta;
    {
        // 100k accounts spread across every shard prefix, decile storage, and
        // 1k code blobs -- the Basic/MultipleShards construction.
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < 100; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        for (uint64_t i = 0; i < 100'000; ++i) {
            StorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    storage.emplace(
                        bytes32_t{j}, StorageDelta{bytes32_t{}, bytes32_t{j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = storage});
        }
        for (uint64_t i = 0; i < 1'000; ++i) {
            std::vector<uint64_t> const bytes(100, i);
            byte_string_view const code{
                reinterpret_cast<unsigned char const *>(bytes.data()),
                bytes.size() * sizeof(uint64_t)};
            bytes32_t const hash = to_bytes(keccak256(code));
            code_delta.emplace(hash, vm::make_shared_intercode(code));
        }
        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            StateDeltas(std::move(deltas)),
            code_delta,
            bytes32_t{BLOCK},
            BlockHeader{.number = BLOCK});
        tdb.finalize(BLOCK, bytes32_t{BLOCK});
        root_hash = tdb.state_root();
    }

    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), BLOCK);
        char const *dbname_paths[] = {src_db.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            /*dump_from_secondary=*/false));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }

    auto load_and_root = [&](unsigned const load_concurrency,
                             unsigned const upsert_concurrency) {
        TempDb const dest_db;
        {
            mpt::Db dest_init{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
            monad::mpt::test::DbAccessor::aux(dest_init)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::primary, state_machine_kind::ethereum);
        }
        char const *dest_paths[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dest_paths,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/false,
            load_concurrency,
            upsert_concurrency,
            /*partition_min_updates=*/upsert_concurrency == 0 ? 0u : 4u);
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        tdb.set_block_and_prefix(BLOCK);
        return tdb.state_root();
    };

    bytes32_t const serial = load_and_root(1u, 0u);
    bytes32_t const parallel = load_and_root(0u, 0u);
    // Parallel prep feeding partitioned merklization: the two features touch
    // the same load, prep on the worker threads and merklization behind the
    // single service thread, so the combination needs its own root check.
    bytes32_t const both = load_and_root(0u, 8u);
    EXPECT_EQ(serial, root_hash);
    EXPECT_EQ(parallel, root_hash);
    EXPECT_EQ(parallel, serial);
    EXPECT_EQ(both, root_hash);
}

// A parallel load into a page-encoded secondary must match a serial one. This
// covers the page-assembly path, which fill_prepared_shard runs per shard on
// the worker threads: slots are grouped into page leaves before the commit.
TEST(DbBinarySnapshot, ParallelLoadMatchesSerialPage)
{
    using namespace monad;
    using namespace monad::mpt;

    constexpr uint64_t BLOCK = 1;
    // Dense slots pack a single page; sparse slots straddle page 0 and page 1
    // (page boundary at slot 0x80, storage_page_t::SLOTS == 128).
    constexpr std::array<uint8_t, 6> DENSE_SLOTS{
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05};
    constexpr std::array<uint8_t, 4> SPARSE_SLOTS{0x00, 0x7f, 0x80, 0x81};

    auto make_slot = [](uint8_t const b) {
        bytes32_t k{};
        k.bytes[31] = b;
        return k;
    };
    auto make_val = [](Address const &a, uint8_t const b) {
        bytes32_t v{};
        v.bytes[30] = a.bytes[19];
        v.bytes[31] = static_cast<uint8_t>(b ^ 0xa5);
        return v;
    };

    TempDb const src_db;
    TempDir const snapshot_dir;

    // Slot-encoded source: 12 accounts spanning multiple shards, alternating
    // dense and sparse storage.
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        load_header({}, db, BlockHeader{.number = 0});
        db.update_finalized_version(0);
        StateDeltas deltas;
        for (uint64_t i = 1; i <= 12; ++i) {
            Address const addr{i};
            StorageDeltas storage;
            auto const add_slot = [&](uint8_t const b) {
                storage.emplace(
                    make_slot(b), StorageDelta{bytes32_t{}, make_val(addr, b)});
            };
            if (i % 2 == 0) {
                for (auto const b : DENSE_SLOTS) {
                    add_slot(b);
                }
            }
            else {
                for (auto const b : SPARSE_SLOTS) {
                    add_slot(b);
                }
            }
            deltas.emplace(
                addr,
                StateDelta{
                    .account = {std::nullopt, Account{.balance = i}},
                    .storage = storage});
        }
        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            deltas,
            Code{},
            bytes32_t{BLOCK},
            BlockHeader{.number = BLOCK});
        tdb.finalize(BLOCK, bytes32_t{BLOCK});
    }

    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), BLOCK);
        char const *dbpath[] = {src_db.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbpath,
            1,
            static_cast<unsigned>(-1),
            BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            /*dump_from_secondary=*/false));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }

    // A shard dir is created only when a shard has data, so the subdirectory
    // count is the number of non-empty shards.
    {
        size_t shard_dirs = 0;
        for (auto const &entry : std::filesystem::directory_iterator{
                 snapshot_dir.path / std::to_string(BLOCK)}) {
            if (entry.is_directory()) {
                ++shard_dirs;
            }
        }
        ASSERT_GE(shard_dirs, 2u) << "test needs a multi-shard snapshot";
    }

    auto page_root = [&](unsigned const load_concurrency) {
        TempDb const dest_db;
        // Fresh db with an activated (empty) page-encoded secondary; the loader
        // opens that secondary, so both handles are dropped before the load.
        // The first open of a fresh inode must not append -- it initializes the
        // storage pool.
        {
            mpt::Db primary{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
            [[maybe_unused]] auto const secondary =
                primary.activate_secondary_timeline(
                    std::make_unique<monad::MonadOnDiskMachine>());
            MONAD_ASSERT(primary.timeline_active(timeline_id::secondary));
        }
        char const *dest_paths[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dest_paths,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/true,
            load_concurrency,
            /*upsert_concurrency=*/0,
            /*partition_min_updates=*/0);

        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {dest_db.path}}};
        {
            auto db2 = db.open_secondary_timeline(
                std::make_unique<monad::MonadOnDiskMachine>());
            MONAD_ASSERT(db2.has_value());
            db = std::move(db2.value());
        }
        TrieDb tdb{db};
        MONAD_ASSERT(tdb.is_page_encoded());
        tdb.set_block_and_prefix(BLOCK);
        return tdb.state_root();
    };

    // Page target plus partitioned merklization is covered by
    // ParallelMerklizationMatchesSerial; this fixture cannot reach a partition
    // (one account per shard, and page encoding collapses an account's slots
    // into a single leaf, so no sublist is ever large enough).
    bytes32_t const serial = page_root(1u);
    bytes32_t const parallel = page_root(0u);
    EXPECT_EQ(parallel, serial);
}
