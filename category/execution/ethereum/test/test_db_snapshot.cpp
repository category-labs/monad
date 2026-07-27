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
#include <category/core/runtime/unaligned.hpp>
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
#include <category/vm/code.hpp>

#include <test_resource_data.h>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ios>
#include <set>
#include <sstream>
#include <string>
#include <utility>
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

    constexpr std::array STREAM_FILES{
        std::pair{"eth_header", MONAD_SNAPSHOT_ETH_HEADER},
        std::pair{"account", MONAD_SNAPSHOT_ACCOUNT},
        std::pair{"storage", MONAD_SNAPSHOT_STORAGE},
        std::pair{"code", MONAD_SNAPSHOT_CODE}};
    static_assert(STREAM_FILES.size() == MONAD_SNAPSHOT_FILES_PER_SHARD);

    monad::byte_string read_file(std::filesystem::path const &path)
    {
        std::ifstream in{path, std::ios::binary};
        MONAD_ASSERT(in.is_open());
        std::stringstream buffer;
        buffer << in.rdbuf();
        auto const bytes = buffer.str();
        return monad::byte_string{
            reinterpret_cast<unsigned char const *>(bytes.data()),
            bytes.size()};
    }

    // Load a snapshot directory the way monad_db_snapshot_load_filesystem does,
    // but with a caller-chosen flush threshold: the smaller it is, the more
    // often the loader writes what it holds mid-shard. A threshold this low is
    // safe to ask for whatever the stream, because the loader ignores it for
    // storage it cannot close page by page. Skips the blake3 verification the
    // filesystem loader does.
    void load_snapshot(
        std::string const &dbname, std::filesystem::path const &root,
        uint64_t const block, uint64_t const flush_bytes,
        bool const load_to_secondary)
    {
        char const *dbname_paths[] = {dbname.c_str()};
        auto *const loader = monad_db_snapshot_loader_create(
            block,
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            load_to_secondary);
        monad_db_snapshot_loader_set_flush_bytes(loader, flush_bytes);
        for (auto const &dir : std::filesystem::directory_iterator{
                 root / std::to_string(block)}) {
            uint64_t const shard = std::stoull(dir.path().stem());
            auto const eth_header = read_file(dir.path() / "eth_header");
            auto const account = read_file(dir.path() / "account");
            auto const storage = read_file(dir.path() / "storage");
            auto const code = read_file(dir.path() / "code");
            auto const ptr = [](monad::byte_string const &b) {
                return b.empty() ? nullptr : b.data();
            };
            monad_db_snapshot_loader_load(
                loader,
                shard,
                ptr(eth_header),
                eth_header.size(),
                ptr(account),
                account.size(),
                ptr(storage),
                storage.size(),
                ptr(code),
                code.size());
        }
        monad_db_snapshot_loader_destroy(loader);
    }

    void write_file(
        std::filesystem::path const &path, monad::byte_string_view const bytes)
    {
        std::ofstream out{path, std::ios::binary | std::ios::trunc};
        MONAD_ASSERT(out.is_open());
        out.write(
            reinterpret_cast<char const *>(bytes.data()),
            static_cast<std::streamsize>(bytes.size()));
        out.close();
        MONAD_ASSERT(out.good());
    }

    // Assert the header is well formed and of `kind`, then remove it, leaving
    // the stream in the layout one predating headers would have. A missing or
    // malformed header fails here rather than corrupting the stripped stream.
    monad::byte_string_view strip_stream_header(
        monad::byte_string_view view, monad_snapshot_type const kind)
    {
        using namespace monad;
        MONAD_ASSERT(view.size() >= sizeof(monad_snapshot_stream_header));
        auto const header =
            unaligned_load<monad_snapshot_stream_header>(view.data());
        MONAD_ASSERT(header.magic == MONAD_SNAPSHOT_STREAM_MAGIC);
        MONAD_ASSERT(header.version == MONAD_SNAPSHOT_STREAM_VERSION);
        MONAD_ASSERT(header.kind == kind);
        MONAD_ASSERT(header.guard == MONAD_SNAPSHOT_STREAM_GUARD);
        view.remove_prefix(sizeof(header));
        return view;
    }

    // Rewrite a grouped storage stream, header already removed, as the
    // ungrouped records of version 1: one account offset per slot entry.
    monad::byte_string ungroup_storage_stream(monad::byte_string_view view)
    {
        using namespace monad;
        byte_string ungrouped;
        while (!view.empty()) {
            MONAD_ASSERT(
                view.size() >= MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE);
            uint64_t const account_offset =
                unaligned_load<uint64_t>(view.data());
            uint32_t const payload_len =
                unaligned_load<uint32_t>(view.data() + sizeof(account_offset));
            view.remove_prefix(MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE);
            byte_string_view payload{view.substr(0, payload_len)};
            view.remove_prefix(payload_len);
            std::array<unsigned char, sizeof(account_offset)> offset_bytes;
            unaligned_store(offset_bytes.data(), account_offset);
            while (!payload.empty()) {
                byte_string_view const before{payload};
                auto const entry = decode_storage_db_raw(payload);
                MONAD_ASSERT(entry.has_value());
                ungrouped.append(offset_bytes.data(), offset_bytes.size());
                ungrouped += before.substr(0, before.size() - payload.size());
            }
        }
        return ungrouped;
    }

    // Rewrite a snapshot in the layout that predates stream headers: no headers
    // anywhere, and one account offset per storage slot entry rather than per
    // group.
    void strip_stream_headers(std::filesystem::path const &version_dir)
    {
        using namespace monad;
        for (auto const &dir :
             std::filesystem::directory_iterator{version_dir}) {
            for (auto const &[name, kind] : STREAM_FILES) {
                auto const path = dir.path() / name;
                auto const stream = read_file(path);
                if (stream.empty()) {
                    continue;
                }
                byte_string_view const stripped{
                    strip_stream_header(stream, kind)};
                write_file(
                    path,
                    kind == MONAD_SNAPSHOT_STORAGE
                        ? byte_string_view{ungroup_storage_stream(stripped)}
                        : stripped);
            }
        }
    }

    monad::byte_string version_1_stream_header(monad_snapshot_type const kind)
    {
        monad_snapshot_stream_header const header{
            .magic = MONAD_SNAPSHOT_STREAM_MAGIC,
            .version = MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED,
            .kind = static_cast<uint8_t>(kind),
            .group_key_shift = 0, // reserved in version 1
            .guard = MONAD_SNAPSHOT_STREAM_GUARD};
        monad::byte_string bytes;
        bytes.resize(sizeof(header));
        monad::unaligned_store(bytes.data(), header);
        return bytes;
    }

    // Rewrite a snapshot as version 1: same headers but for the version byte,
    // and a storage stream whose records hold one slot entry each.
    void downgrade_to_version_1(std::filesystem::path const &version_dir)
    {
        using namespace monad;
        for (auto const &dir :
             std::filesystem::directory_iterator{version_dir}) {
            for (auto const &[name, kind] : STREAM_FILES) {
                auto const path = dir.path() / name;
                auto const stream = read_file(path);
                if (stream.empty()) {
                    continue;
                }
                byte_string_view const stripped{
                    strip_stream_header(stream, kind)};
                byte_string rewritten{version_1_stream_header(kind)};
                rewritten += kind == MONAD_SNAPSHOT_STORAGE
                                 ? ungroup_storage_stream(stripped)
                                 : byte_string{stripped};
                write_file(path, rewritten);
            }
        }
    }

    struct StorageGroup
    {
        uint64_t account_offset;
        monad::bytes32_t page_key;
        size_t slots;
    };

    // Split a storage stream into its groups, asserting that each holds the
    // slots of exactly one page in ascending key order.
    std::vector<StorageGroup> parse_storage_stream(
        monad::byte_string_view view, uint8_t const expected_group_key_shift)
    {
        using namespace monad;
        MONAD_ASSERT(view.size() >= sizeof(monad_snapshot_stream_header));
        auto const header =
            unaligned_load<monad_snapshot_stream_header>(view.data());
        EXPECT_EQ(header.magic, MONAD_SNAPSHOT_STREAM_MAGIC);
        EXPECT_EQ(header.version, MONAD_SNAPSHOT_STREAM_VERSION);
        EXPECT_EQ(header.kind, MONAD_SNAPSHOT_STORAGE);
        EXPECT_EQ(header.group_key_shift, expected_group_key_shift);
        view.remove_prefix(sizeof(header));

        std::vector<StorageGroup> groups;
        while (!view.empty()) {
            MONAD_ASSERT(
                view.size() >= MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE);
            uint64_t const account_offset =
                unaligned_load<uint64_t>(view.data());
            uint32_t const payload_len =
                unaligned_load<uint32_t>(view.data() + sizeof(account_offset));
            view.remove_prefix(MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE);
            EXPECT_LE(payload_len, view.size());
            byte_string_view payload{view.substr(0, payload_len)};
            view.remove_prefix(payload_len);

            StorageGroup group{account_offset, bytes32_t{}, 0};
            bytes32_t last_slot_key{};
            while (!payload.empty()) {
                auto const entry = decode_storage_db_raw(payload);
                EXPECT_TRUE(entry.has_value());
                bytes32_t const slot_key = to_bytes(entry.value().first);
                if (group.slots == 0) {
                    group.page_key = compute_page_key(slot_key);
                }
                else {
                    EXPECT_GT(slot_key, last_slot_key);
                    EXPECT_EQ(compute_page_key(slot_key), group.page_key);
                }
                last_slot_key = slot_key;
                ++group.slots;
            }
            EXPECT_GT(group.slots, 0u);
            groups.push_back(group);
        }
        return groups;
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
            /*load_to_secondary=*/false);
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
            /*load_to_secondary=*/false);
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
            /*load_to_secondary=*/true);
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

namespace
{
    constexpr uint64_t PAGE_BLOCK = 1;
    // Raw slot keys 0x00-0x7f share page 0, 0x80-0xff page 1, and so on, so
    // every account spans four pages, two of which hold more than one slot.
    constexpr std::array<uint16_t, 8> PAGE_SLOTS{
        0x0000, 0x0001, 0x0002, 0x007f, 0x0080, 0x0081, 0x0100, 0x01ff};
    constexpr size_t PAGES_PER_ACCOUNT = 4;
    constexpr size_t MULTI_SLOT_PAGES_PER_ACCOUNT = 2;
    // Address{5} and Address{15} hash into the same shard, so one of them
    // writes its storage groups at a non-zero account offset: with one account
    // per shard every offset is zero and a loader that ignored the field would
    // pass.
    std::array<monad::Address, 6> const PAGE_ADDRS{
        monad::Address{1},
        monad::Address{2},
        monad::Address{3},
        monad::Address{4},
        monad::Address{5},
        monad::Address{15}};

    monad::bytes32_t page_slot_key(uint16_t const raw)
    {
        monad::bytes32_t key{};
        key.bytes[30] = static_cast<uint8_t>(raw >> 8);
        key.bytes[31] = static_cast<uint8_t>(raw & 0xff);
        return key;
    }

    monad::bytes32_t
    page_slot_value(monad::Address const &addr, uint16_t const raw)
    {
        monad::bytes32_t value{};
        value.bytes[29] = addr.bytes[19];
        value.bytes[30] = static_cast<uint8_t>(raw >> 8);
        value.bytes[31] = static_cast<uint8_t>((raw & 0xff) ^ 0xa5);
        return value;
    }

    monad::byte_string page_code(monad::Address const &addr)
    {
        return monad::byte_string(64, addr.bytes[19]);
    }

    // Populate the page-encoded secondary timeline of `dbname` and return its
    // state root.
    monad::bytes32_t build_page_source(std::string const &dbname)
    {
        using namespace monad;
        using namespace monad::mpt;

        mpt::Db db1{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dbname}}};
        // Activate before any TrieDb exists (requires worker_thread_use_count
        // == 1).
        mpt::Db db2 = db1.activate_secondary_timeline(
            std::make_unique<monad::MonadOnDiskMachine>());
        load_header({}, db2, BlockHeader{.number = 0});
        db2.update_finalized_version(0);

        StateDeltas deltas;
        Code code_delta;
        for (auto const &addr : PAGE_ADDRS) {
            StorageDeltas storage;
            for (auto const raw : PAGE_SLOTS) {
                storage.emplace(
                    page_slot_key(raw),
                    StorageDelta{bytes32_t{}, page_slot_value(addr, raw)});
            }
            auto const code = page_code(addr);
            bytes32_t const code_hash = to_bytes(keccak256(code));
            code_delta.emplace(code_hash, vm::make_shared_intercode(code));
            deltas.emplace(
                addr,
                StateDelta{
                    .account =
                        {std::nullopt,
                         Account{.balance = 1, .code_hash = code_hash}},
                    .storage = storage});
        }
        TrieDb tdb2{db2};
        MONAD_ASSERT(tdb2.is_page_encoded());
        PageCommitBuilder builder(PAGE_BLOCK, tdb2);
        builder.add_state_deltas(deltas).add_code(code_delta);
        BlockHeader const header{.number = PAGE_BLOCK};
        tdb2.commit(
            bytes32_t{PAGE_BLOCK},
            builder,
            header,
            deltas,
            [&](BlockHeader &h) {
                h.receipts_root = tdb2.receipts_root();
                h.state_root = tdb2.state_root();
                h.withdrawals_root = tdb2.withdrawals_root();
                h.transactions_root = tdb2.transactions_root();
            });
        tdb2.finalize(PAGE_BLOCK, bytes32_t{PAGE_BLOCK});
        return tdb2.state_root();
    }

    // Populate the slot-encoded primary timeline of `dbname` with the same
    // state build_page_source puts on a page-encoded secondary, so a restore of
    // either dump into a page-encoded target must reach the same root.
    void build_slot_source(std::string const &dbname)
    {
        using namespace monad;
        using namespace monad::mpt;

        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dbname}}};
        load_header({}, db, BlockHeader{.number = 0});
        db.update_finalized_version(0);

        StateDeltas deltas;
        Code code_delta;
        for (auto const &addr : PAGE_ADDRS) {
            StorageDeltas storage;
            for (auto const raw : PAGE_SLOTS) {
                storage.emplace(
                    page_slot_key(raw),
                    StorageDelta{bytes32_t{}, page_slot_value(addr, raw)});
            }
            auto const code = page_code(addr);
            bytes32_t const code_hash = to_bytes(keccak256(code));
            code_delta.emplace(code_hash, vm::make_shared_intercode(code));
            deltas.emplace(
                addr,
                StateDelta{
                    .account =
                        {std::nullopt,
                         Account{.balance = 1, .code_hash = code_hash}},
                    .storage = storage});
        }
        TrieDb tdb{db};
        MONAD_ASSERT(!tdb.is_page_encoded());
        monad::test::commit_simple(
            tdb,
            deltas,
            code_delta,
            bytes32_t{PAGE_BLOCK},
            BlockHeader{.number = PAGE_BLOCK});
        tdb.finalize(PAGE_BLOCK, bytes32_t{PAGE_BLOCK});
    }

    void dump_source(
        std::string const &dbname, std::filesystem::path const &root,
        bool const from_secondary)
    {
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                root.c_str(), PAGE_BLOCK);
        char const *paths[] = {dbname.c_str()};
        EXPECT_TRUE(monad_db_dump_snapshot(
            paths,
            1,
            static_cast<unsigned>(-1),
            PAGE_BLOCK,
            monad_db_snapshot_write_filesystem,
            context,
            2048,
            1,
            0,
            from_secondary));
        monad_db_snapshot_filesystem_write_user_context_destroy(context);
    }

    void dump_page_source(
        std::string const &dbname, std::filesystem::path const &root)
    {
        dump_source(dbname, root, /*from_secondary=*/true);
    }

    void dump_slot_source(
        std::string const &dbname, std::filesystem::path const &root)
    {
        dump_source(dbname, root, /*from_secondary=*/false);
    }

    void activate_page_secondary(std::string const &dbname)
    {
        using namespace monad;
        using namespace monad::mpt;
        mpt::Db primary{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dbname}}};
        [[maybe_unused]] auto const secondary =
            primary.activate_secondary_timeline(
                std::make_unique<monad::MonadOnDiskMachine>());
        MONAD_ASSERT(primary.timeline_active(timeline_id::secondary));
    }

    void verify_page_restore(
        std::string const &dbname, monad::bytes32_t const &expected_root)
    {
        using namespace monad;
        using namespace monad::mpt;

        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
        {
            auto db2 = db.open_secondary_timeline(
                std::make_unique<monad::MonadOnDiskMachine>());
            ASSERT_TRUE(db2.has_value());
            db = std::move(db2.value());
        }
        TrieDb tdb{db};
        ASSERT_TRUE(tdb.is_page_encoded());
        tdb.set_block_and_prefix(PAGE_BLOCK);
        EXPECT_EQ(tdb.state_root(), expected_root);

        Incarnation const inc{0, 0};
        for (auto const &addr : PAGE_ADDRS) {
            ASSERT_TRUE(tdb.read_account(addr).has_value());
            for (auto const raw : PAGE_SLOTS) {
                EXPECT_EQ(
                    tdb.read_storage(addr, inc, page_slot_key(raw)),
                    page_slot_value(addr, raw))
                    << "addr=" << static_cast<int>(addr.bytes[19]) << " slot=0x"
                    << std::hex << raw;
            }
        }

        auto const state_cursor =
            db.find(concat(finalized_nibbles, STATE_NIBBLE), PAGE_BLOCK);
        ASSERT_TRUE(state_cursor.has_value());
        LeafCounter counter;
        ASSERT_TRUE(
            db.traverse_blocking(state_cursor.value(), counter, PAGE_BLOCK));
        EXPECT_EQ(counter.count, PAGE_ADDRS.size() * PAGES_PER_ACCOUNT);
    }

    // Restore `root` into a fresh slot-encoded primary at the smallest
    // threshold there is, and check every slot of every account round-trips.
    void restore_and_verify_slot_target(
        std::string const &dbname, std::filesystem::path const &root)
    {
        using namespace monad;
        using namespace monad::mpt;

        {
            mpt::Db dest_init{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.dbname_paths = {dbname}}};
            monad::mpt::test::DbAccessor::aux(dest_init)
                .metadata_ctx()
                .set_state_machine_kind(
                    timeline_id::primary, state_machine_kind::ethereum);
        }
        load_snapshot(
            dbname,
            root,
            PAGE_BLOCK,
            /*flush_bytes=*/1,
            /*load_to_secondary=*/false);

        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        ASSERT_FALSE(tdb.is_page_encoded());
        tdb.set_block_and_prefix(PAGE_BLOCK);
        Incarnation const inc{0, 0};
        for (auto const &addr : PAGE_ADDRS) {
            ASSERT_TRUE(tdb.read_account(addr).has_value());
            for (auto const raw : PAGE_SLOTS) {
                EXPECT_EQ(
                    tdb.read_storage(addr, inc, page_slot_key(raw)),
                    page_slot_value(addr, raw))
                    << "addr=" << static_cast<int>(addr.bytes[19]) << " slot=0x"
                    << std::hex << raw;
            }
        }
    }
}

// Every stream a shard writes opens with a header naming its version and kind.
TEST(DbBinarySnapshot, SnapshotStreamHeaders)
{
    TempDb const src_db;
    TempDir const snapshot_dir;

    build_page_source(src_db.path);
    dump_page_source(src_db.path, snapshot_dir.path);

    std::array<size_t, MONAD_SNAPSHOT_FILES_PER_SHARD> headers_checked{};
    for (auto const &dir : std::filesystem::directory_iterator{
             snapshot_dir.path / std::to_string(PAGE_BLOCK)}) {
        for (auto const &[name, kind] : STREAM_FILES) {
            auto const stream = read_file(dir.path() / name);
            if (stream.empty()) {
                continue;
            }
            // Asserts the header is well formed and of this stream's kind.
            EXPECT_LT(strip_stream_header(stream, kind).size(), stream.size());
            ++headers_checked.at(kind);
        }
    }
    for (auto const &[name, kind] : STREAM_FILES) {
        EXPECT_GT(headers_checked.at(kind), 0u) << name;
    }
}

// A page-encoded source dumps the slots of each page as one closed group, which
// is what lets a page-encoded target write pages out as it reads.
TEST(DbBinarySnapshot, PageGroupedStorageStream)
{
    using namespace monad;

    TempDb const src_db;
    TempDir const snapshot_dir;

    build_page_source(src_db.path);
    dump_page_source(src_db.path, snapshot_dir.path);

    size_t total_groups = 0;
    size_t total_slots = 0;
    size_t multi_slot_groups = 0;
    size_t groups_past_the_first_account = 0;
    for (auto const &dir : std::filesystem::directory_iterator{
             snapshot_dir.path / std::to_string(PAGE_BLOCK)}) {
        auto const storage = read_file(dir.path() / "storage");
        if (storage.empty()) {
            continue;
        }
        auto const groups =
            parse_storage_stream(storage, storage_page_t::PAGE_KEY_SHIFT);
        std::set<std::pair<uint64_t, bytes32_t>> seen;
        for (auto const &group : groups) {
            EXPECT_TRUE(
                seen.emplace(group.account_offset, group.page_key).second)
                << "page spread over more than one group";
            total_slots += group.slots;
            if (group.slots > 1) {
                ++multi_slot_groups;
            }
            if (group.account_offset != 0) {
                ++groups_past_the_first_account;
            }
        }
        total_groups += groups.size();
    }
    EXPECT_EQ(total_groups, PAGE_ADDRS.size() * PAGES_PER_ACCOUNT);
    EXPECT_EQ(total_slots, PAGE_ADDRS.size() * PAGE_SLOTS.size());
    EXPECT_EQ(
        multi_slot_groups, PAGE_ADDRS.size() * MULTI_SLOT_PAGES_PER_ACCOUNT);
    // Two of PAGE_ADDRS share a shard, so the offset field is exercised rather
    // than being zero everywhere.
    EXPECT_GT(groups_past_the_first_account, 0u);
}

// Restore a page-encoded snapshot into a page-encoded target twice: once
// flushing at every group boundary, once with the default threshold, which a
// snapshot this small never reaches, so it flushes only when the load ends.
// Both must reproduce the source root, which is what makes the threshold a pure
// memory knob.
TEST(DbBinarySnapshot, PageToPageRestoreIndependentOfFlushThreshold)
{
    using namespace monad;

    TempDb const src_db;
    TempDb const per_page_db;
    TempDb const per_shard_db;
    TempDir const snapshot_dir;

    bytes32_t const source_root = build_page_source(src_db.path);
    dump_page_source(src_db.path, snapshot_dir.path);

    activate_page_secondary(per_page_db.path);
    load_snapshot(
        per_page_db.path,
        snapshot_dir.path,
        PAGE_BLOCK,
        /*flush_bytes=*/1,
        /*load_to_secondary=*/true);
    verify_page_restore(per_page_db.path, source_root);

    activate_page_secondary(per_shard_db.path);
    char const *dest_paths[] = {per_shard_db.path.c_str()};
    monad_db_snapshot_load_filesystem(
        dest_paths,
        1,
        static_cast<unsigned>(-1),
        snapshot_dir.path.c_str(),
        PAGE_BLOCK,
        /*load_to_secondary=*/true);
    verify_page_restore(per_shard_db.path, source_root);
}

// A snapshot with no stream headers at all — the layout dumped before they
// existed — still restores into either encoding, buffering the shard for a
// page-encoded target as it always did.
TEST(DbBinarySnapshot, HeaderlessSnapshotRestores)
{
    using namespace monad;
    using namespace monad::mpt;

    TempDb const src_db;
    TempDb const page_db;
    TempDb const slot_db;
    TempDir const snapshot_dir;

    bytes32_t const source_root = build_page_source(src_db.path);
    dump_page_source(src_db.path, snapshot_dir.path);
    strip_stream_headers(snapshot_dir.path / std::to_string(PAGE_BLOCK));

    // A shift of zero tells the loader nothing about where pages end, so the
    // one byte threshold must not tempt it into writing a page before the shard
    // is read out.
    activate_page_secondary(page_db.path);
    load_snapshot(
        page_db.path,
        snapshot_dir.path,
        PAGE_BLOCK,
        /*flush_bytes=*/1,
        /*load_to_secondary=*/true);
    verify_page_restore(page_db.path, source_root);

    restore_and_verify_slot_target(slot_db.path, snapshot_dir.path);
}

// A version 1 snapshot — headers throughout, but a storage stream whose records
// hold one slot each — restores into either encoding. This is the layout of a
// snapshot dumped after stream headers landed and before grouping did.
TEST(DbBinarySnapshot, Version1SnapshotRestores)
{
    using namespace monad;

    TempDb const src_db;
    TempDb const page_db;
    TempDb const slot_db;
    TempDir const snapshot_dir;

    bytes32_t const source_root = build_page_source(src_db.path);
    dump_page_source(src_db.path, snapshot_dir.path);
    downgrade_to_version_1(snapshot_dir.path / std::to_string(PAGE_BLOCK));

    // Version 1 leaves the shift byte reserved, so the loader must not read a
    // page-closing promise out of it however small the threshold.
    activate_page_secondary(page_db.path);
    load_snapshot(
        page_db.path,
        snapshot_dir.path,
        PAGE_BLOCK,
        /*flush_bytes=*/1,
        /*load_to_secondary=*/true);
    verify_page_restore(page_db.path, source_root);

    restore_and_verify_slot_target(slot_db.path, snapshot_dir.path);
}

// A snapshot dumped from a slot-encoded db is grouped, but every group holds
// one slot, so the loader cannot close a target page as it reads and must hold
// the shard however small the threshold. Restoring it into a page-encoded
// target has to reach the same root as restoring a page-encoded dump of the
// same state.
TEST(DbBinarySnapshot, SlotSourceToPageTargetIgnoresFlushThreshold)
{
    using namespace monad;

    TempDb const page_src_db;
    TempDb const slot_src_db;
    TempDb const dest_db;
    TempDir const snapshot_dir;

    bytes32_t const page_root = build_page_source(page_src_db.path);
    build_slot_source(slot_src_db.path);
    dump_slot_source(slot_src_db.path, snapshot_dir.path);

    size_t storage_streams = 0;
    for (auto const &dir : std::filesystem::directory_iterator{
             snapshot_dir.path / std::to_string(PAGE_BLOCK)}) {
        auto const storage = read_file(dir.path() / "storage");
        if (storage.empty()) {
            continue;
        }
        for (auto const &group : parse_storage_stream(storage, 0)) {
            EXPECT_EQ(group.slots, 1u) << "a slot leaf holds one slot";
        }
        ++storage_streams;
    }
    EXPECT_GT(storage_streams, 0u);

    activate_page_secondary(dest_db.path);
    load_snapshot(
        dest_db.path,
        snapshot_dir.path,
        PAGE_BLOCK,
        /*flush_bytes=*/1,
        /*load_to_secondary=*/true);
    verify_page_restore(dest_db.path, page_root);
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
    TempDb const flushing_dest_db;
    TempDir const snapshot_dir;

    auto const stamp_slot_target = [](std::string const &dbname) {
        mpt::Db dest_init{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.dbname_paths = {dbname}}};
        monad::mpt::test::DbAccessor::aux(dest_init)
            .metadata_ctx()
            .set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
    };

    // Verify the target is slot-encoded and every slot round-trips.
    auto const verify_slots = [&](std::string const &dbname) {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
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
    };

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

        stamp_slot_target(dest_db.path);
        char const *dest_path[] = {dest_db.path.c_str()};
        monad_db_snapshot_load_filesystem(
            dest_path,
            1,
            static_cast<unsigned>(-1),
            snapshot_dir.path.c_str(),
            BLOCK,
            /*load_to_secondary=*/false);
    }

    verify_slots(dest_db.path);

    // The same multi-slot groups into a slot-encoded target, flushing after
    // every group: a slot leaf stands alone, so nothing depends on the group
    // surviving until the end of the shard.
    stamp_slot_target(flushing_dest_db.path);
    load_snapshot(
        flushing_dest_db.path,
        snapshot_dir.path,
        BLOCK,
        /*flush_bytes=*/1,
        /*load_to_secondary=*/false);
    verify_slots(flushing_dest_db.path);
}
