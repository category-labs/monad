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

#include <gtest/gtest.h>

#ifdef MONAD_HAVE_ROCKSDB

    #include <category/async/util.hpp>
    #include <category/core/assert.h>
    #include <category/core/byte_string.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/keccak.hpp>
    #include <category/execution/ethereum/core/account.hpp>
    #include <category/execution/ethereum/core/block.hpp>
    #include <category/execution/ethereum/db/db_snapshot.h>
    #include <category/execution/ethereum/db/db_snapshot_filesystem.h>
    #include <category/execution/ethereum/db/snapshot_loader.hpp>
    #include <category/execution/ethereum/db/trie_db.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/mpt/db.hpp>
    #include <category/mpt/ondisk_db_config.hpp>
    #include <category/statedb/kv_store.hpp>
    #include <category/statedb/schema.hpp>
    #include <category/vm/vm.hpp>

    #include <test_resource_data.h>

    #include <cstring>
    #include <filesystem>
    #include <memory>
    #include <string>
    #include <vector>

using namespace monad;

namespace
{
    struct TempDb
    {
        int fd;
        std::string path;

        TempDb()
            : fd{MONAD_ASYNC_NAMESPACE::make_temporary_inode()}
            , path{"/proc/self/fd/" + std::to_string(fd)}
        {
            MONAD_ASSERT(
                -1 !=
                ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
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
                "monad_seed_test_XXXXXX";
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

    byte_string_view meta_bsv(std::string_view const s)
    {
        return byte_string_view{
            reinterpret_cast<unsigned char const *>(s.data()), s.size()};
    }
}

// Dump a small MonadDB state to a filesystem snapshot, seed a RocksDB store
// from it via the F8 loader, and confirm the seed gate (state_root) plus the
// flat / code / meta column families.
TEST(SnapshotLoader, SeedAndGate)
{
    using namespace monad::mpt;

    constexpr uint64_t N = 10;
    TempDb const src;
    TempDir const snapshot_dir;
    TempDir const rocksdb_dir;

    bytes32_t root_hash;
    Code code_delta;
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {src.path}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < N; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(N - 1);

        StateDeltas deltas;
        for (uint64_t i = 0; i < 20; ++i) {
            StorageDeltas storage;
            if ((i % 5) == 0) {
                for (uint64_t j = 0; j < 3; ++j) {
                    storage.emplace(
                        bytes32_t{j + 1},
                        StorageDelta{bytes32_t{}, bytes32_t{0x10 + j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt,
                         Account{.balance = i + 1, .nonce = i + 1}},
                    .storage = storage});
        }
        for (uint64_t i = 0; i < 3; ++i) {
            std::vector<uint64_t> const bytes(40, i + 1);
            byte_string_view const code{
                reinterpret_cast<unsigned char const *>(bytes.data()),
                bytes.size() * sizeof(uint64_t)};
            code_delta.emplace(
                to_bytes(keccak256(code)), vm::make_shared_intercode(code));
        }

        TrieDb tdb{db};
        monad::test::commit_simple(
            tdb,
            monad::test::sd(std::move(deltas)),
            code_delta,
            bytes32_t{N},
            BlockHeader{.number = N});
        tdb.finalize(N, bytes32_t{N});
        root_hash = tdb.state_root();
    }

    // Dump to a filesystem snapshot (single shard).
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), N);
        char const *dbname_paths[] = {src.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            N,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }

    // F8: seed RocksDB from the snapshot. The internal gate asserts the
    // converted state_root equals block N's ETH_HEADER stateRoot.
    bytes32_t const seeded =
        seed_rocksdb_from_snapshot(snapshot_dir.path, N, rocksdb_dir.path);
    EXPECT_EQ(seeded, root_hash);

    // Inspect the resulting CFs.
    auto kv = statedb::KvStore::open(rocksdb_dir.path);

    // CF_META: the persisted state root matches.
    auto const meta_root =
        kv->get(statedb::Cf::meta, meta_bsv(statedb::meta_key::state_root));
    ASSERT_TRUE(meta_root.has_value());
    ASSERT_EQ(meta_root->size(), sizeof(bytes32_t));
    bytes32_t persisted{};
    std::memcpy(persisted.bytes, meta_root->data(), sizeof(bytes32_t));
    EXPECT_EQ(persisted, root_hash);

    // CF_FLAT_STATE: a sampled account round-trips (raw-Address key, value is
    // the address-prefixed account encoding).
    Address const a7{7};
    byte_string const a7_key{a7.bytes, sizeof(a7.bytes)};
    auto const flat = kv->get(statedb::Cf::flat_state, a7_key);
    ASSERT_TRUE(flat.has_value());
    byte_string_view flat_view{*flat};
    auto const decoded = decode_account_db_ignore_address(flat_view);
    ASSERT_FALSE(decoded.has_error());
    EXPECT_EQ(decoded.value().nonce, 8u);
    EXPECT_EQ(decoded.value().balance, 8u);

    // CF_CODE: a sampled code is present.
    std::vector<uint64_t> const bytes(40, 1);
    byte_string_view const code{
        reinterpret_cast<unsigned char const *>(bytes.data()),
        bytes.size() * sizeof(uint64_t)};
    auto const stored_code =
        kv->get(statedb::Cf::code, to_bytes(keccak256(code)));
    ASSERT_TRUE(stored_code.has_value());
    EXPECT_EQ(byte_string_view{*stored_code}, code);

    // CF_TRIE_NODES: the state-root node is present (non-trivial trie).
    auto const root_node = kv->get(statedb::Cf::trie_nodes, root_hash);
    EXPECT_TRUE(root_node.has_value());
}

#else

TEST(SnapshotLoader, SkippedWithoutRocksDb)
{
    GTEST_SKIP() << "requires -DMONAD_ENABLE_ROCKSDB=ON";
}

#endif // MONAD_HAVE_ROCKSDB
