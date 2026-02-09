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
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/storage_page.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <filesystem>

namespace
{
    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_db_snapshot_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        monad::OnDiskMachine machine;
        monad::mpt::Db const db{
            machine,
            monad::mpt::OnDiskDbConfig{
                .append = false, .dbname_paths = {path}}};
        return dbname;
    }
}

TEST(DbBinarySnapshot, Basic)
{
    using namespace monad;
    using namespace monad::mpt;

    auto const src_db = tmp_dbname();

    Code code_delta;
    BlockHeader last_header;
    {
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < 100; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        for (uint64_t i = 0; i < 100'000; ++i) {
            PageStorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    bytes32_t const slot_key{j};
                    bytes32_t const page_key = compute_page_key(slot_key);
                    uint8_t const slot_offset = compute_slot_offset(slot_key);
                    PageStorageDeltas::accessor acc;
                    if (!storage.find(acc, page_key)) {
                        storage.emplace(acc, page_key, PageStorageDelta{});
                    }
                    acc->second.second[slot_offset] = bytes32_t{j};
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = std::move(storage)});
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
        tdb.commit(
            deltas, code_delta, bytes32_t{100}, BlockHeader{.number = 100});
        tdb.finalize(100, bytes32_t{100});
        last_header = tdb.read_eth_header();
    }

    auto const dest_db = tmp_dbname();
    {
        auto const root = std::filesystem::temp_directory_path() / "snapshot";
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                root.c_str(), 100);
        char const *dbname_paths[] = {src_db.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            100,
            monad_db_snapshot_write_filesystem,
            context,
            2048, // dump_concurrency_limit
            1, // total_shards
            0)); // shard_number

        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        char const *dbname_paths_new[] = {dest_db.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new, 1, static_cast<unsigned>(-1), root.c_str(), 100);

        std::filesystem::remove_all(root);
    }

    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.set_block_and_prefix(i);
            EXPECT_EQ(tdb.read_eth_header(), BlockHeader{.number = i});
        }
        tdb.set_block_and_prefix(100);
        EXPECT_EQ(tdb.read_eth_header(), last_header);
        for (uint64_t i = 0; i < 100'000; ++i) {
            if ((i % 100) == 0) {
                for (uint64_t j = 1; j < 10; ++j) {
                    auto const val = tdb.read_storage(Address{i}, Incarnation{0, 0}, bytes32_t{j});
                    EXPECT_EQ(val, bytes32_t{j})
                        << "Mismatch at account=" << i << " slot=" << j;
                }
            }
        }
        for (auto const &[hash, icode] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(
                byte_string_view(from_db->code(), from_db->size()),
                byte_string_view(icode->code(), icode->size()));
        }
    }

    std::filesystem::remove(src_db);
    std::filesystem::remove(dest_db);
}

TEST(DbBinarySnapshot, MultipleShards)
{
    using namespace monad;
    using namespace monad::mpt;

    auto const src_db = tmp_dbname();

    Code code_delta;
    BlockHeader last_header;
    {
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db}}};
        Node::SharedPtr root{};
        for (uint64_t i = 0; i < 100; ++i) {
            root = load_header(std::move(root), db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        for (uint64_t i = 0; i < 100'000; ++i) {
            PageStorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    bytes32_t const slot_key{j};
                    bytes32_t const page_key = compute_page_key(slot_key);
                    uint8_t const slot_offset = compute_slot_offset(slot_key);
                    PageStorageDeltas::accessor acc;
                    if (!storage.find(acc, page_key)) {
                        storage.emplace(acc, page_key, PageStorageDelta{});
                    }
                    acc->second.second[slot_offset] = bytes32_t{j};
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = std::move(storage)});
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
        tdb.commit(
            deltas, code_delta, bytes32_t{100}, BlockHeader{.number = 100});
        tdb.finalize(100, bytes32_t{100});
        last_header = tdb.read_eth_header();
    }

    auto const dest_db = tmp_dbname();
    {
        constexpr uint64_t NUM_SHARDS = 4;
        std::filesystem::path const base_root =
            std::filesystem::temp_directory_path() / "snapshot_sharded";

        if (std::filesystem::exists(base_root)) {
            std::filesystem::remove_all(base_root);
        }
        std::filesystem::create_directories(base_root);

        std::vector<std::filesystem::path> shard_roots;
        for (uint64_t shard = 0; shard < NUM_SHARDS; ++shard) {
            auto const shard_root =
                base_root / ("shard_" + std::to_string(shard));
            shard_roots.push_back(shard_root);

            auto *const context =
                monad_db_snapshot_filesystem_write_user_context_create(
                    shard_root.c_str(), 100);
            char const *dbname_paths[] = {src_db.c_str()};
            EXPECT_TRUE(monad_db_dump_snapshot(
                dbname_paths,
                1,
                static_cast<unsigned>(-1),
                100,
                monad_db_snapshot_write_filesystem,
                context,
                2048, // dump_concurrency_limit
                NUM_SHARDS,
                shard));

            monad_db_snapshot_filesystem_write_user_context_destroy(context);
        }

        auto const combined_root =
            std::filesystem::temp_directory_path() / "snapshot_combined";

        if (std::filesystem::exists(combined_root)) {
            std::filesystem::remove_all(combined_root);
        }

        auto const combined_version_dir = combined_root / "100";
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
        char const *dbname_paths_new[] = {dest_db.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new,
            1,
            static_cast<unsigned>(-1),
            combined_root.c_str(),
            100);

        std::filesystem::remove_all(base_root);
        std::filesystem::remove_all(combined_root);
    }
    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.set_block_and_prefix(i);
            EXPECT_EQ(tdb.read_eth_header(), BlockHeader{.number = i});
        }
        tdb.set_block_and_prefix(100);
        EXPECT_EQ(tdb.read_eth_header(), last_header);
        for (uint64_t i = 0; i < 100'000; ++i) {
            if ((i % 100) == 0) {
                for (uint64_t j = 1; j < 10; ++j) {
                    auto const val = tdb.read_storage(Address{i}, Incarnation{0, 0}, bytes32_t{j});
                    EXPECT_EQ(val, bytes32_t{j})
                        << "Mismatch at account=" << i << " slot=" << j;
                }
            }
        }
        for (auto const &[hash, icode] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(
                byte_string_view(from_db->code(), from_db->size()),
                byte_string_view(icode->code(), icode->size()));
        }
    }

    std::filesystem::remove(src_db);
    std::filesystem::remove(dest_db);
}
