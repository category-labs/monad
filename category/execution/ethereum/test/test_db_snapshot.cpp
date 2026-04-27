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
#include <category/execution/monad/db/page_storage_broker.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>

#include <test_resource_data.h>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <filesystem>

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
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db.path}}};
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
            deltas,
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
            0)); // shard_number

        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        {
            OnDiskMachine machine;
            mpt::Db dest_init{
                machine, OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        }
        char const *dbname_paths_new[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            100,
            /*page_mode=*/false);
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
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db.path}}};
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
            deltas,
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
                shard));

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
            OnDiskMachine machine;
            mpt::Db dest_init{
                machine, OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        }
        char const *dbname_paths_new[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new,
            1,
            static_cast<unsigned>(-1),
            combined_root.path.c_str(),
            100,
            /*page_mode=*/false);
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

        bool down(
            unsigned char const branch, monad::mpt::Node const &node) override
        {
            if (branch == monad::mpt::INVALID_BRANCH) {
                return true;
            }
            depth = static_cast<uint8_t>(
                depth + 1 + node.path_nibbles_len());
            if (depth == STORAGE_LEAF_DEPTH && node.has_value()) {
                ++count;
            }
            return true;
        }

        void up(
            unsigned char const branch, monad::mpt::Node const &node) override
        {
            if (branch == monad::mpt::INVALID_BRANCH) {
                return;
            }
            depth = static_cast<uint8_t>(
                depth - 1 - node.path_nibbles_len());
        }

        std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<LeafCounter>(*this);
        }
    };
}

TEST(DbBinarySnapshot, LoadPageMode)
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

    TempDb const src_db;
    TempDb const dest_db;
    TempDir const snapshot_dir;

    // Build slot-encoded source db with two accounts.
    {
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db.path}}};
        load_header({}, db, BlockHeader{.number = 0});
        db.update_finalized_version(0);
        StateDeltas deltas;
        for (auto const &addr : ADDRS) {
            StorageDeltas storage;
            for (auto const b : SLOT_BYTES) {
                storage.emplace(
                    make_slot(b),
                    StorageDelta{bytes32_t{}, make_val(addr, b)});
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

    // Dump slot-encoded snapshot, then init dest db with MonadOnDiskMachine
    // (page mode requires it) and load with page_mode=true.
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                snapshot_dir.path.c_str(), BLOCK);
        char const *src_paths[] = {src_db.path.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            src_paths,
            1,
            static_cast<unsigned>(-1),
            BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        {
            MonadOnDiskMachine machine;
            mpt::Db dest_init{
                machine, OnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        }
        char const *dest_paths[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dest_paths,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*page_mode=*/true);
    }

    // Verify dest db is page-encoded and round-trip slot reads match.
    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db.path}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        tdb.set_block_and_prefix(BLOCK);
        Incarnation const inc{0, 0};
        PageStorageBroker broker{tdb};

        for (auto const &addr : ADDRS) {
            ASSERT_TRUE(tdb.read_account(addr).has_value());
            for (auto const b : SLOT_BYTES) {
                EXPECT_EQ(
                    broker.read_storage_slot(addr, inc, make_slot(b)),
                    make_val(addr, b))
                    << "addr=" << static_cast<int>(addr.bytes[19])
                    << " slot=0x" << std::hex << static_cast<int>(b);
            }

            auto const page0 =
                broker.read_storage_page(addr, inc, bytes32_t{});
            EXPECT_EQ(page0[0], make_val(addr, 0x00));
            EXPECT_EQ(page0[1], make_val(addr, 0x01));
            EXPECT_EQ(page0[0x7f], make_val(addr, 0x7f));
            for (size_t i = 2; i < 0x7f; ++i) {
                EXPECT_EQ(page0[static_cast<uint8_t>(i)], bytes32_t{});
            }

            bytes32_t const pk1 = compute_page_key(make_slot(0x80));
            auto const page1 = broker.read_storage_page(addr, inc, pk1);
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
                    broker.read_storage_page(addr, inc, page_key));
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
        ASSERT_TRUE(
            db.traverse_blocking(state_cursor.value(), counter, BLOCK));
        EXPECT_EQ(counter.count, ADDRS.size() * 2);
    }
}
