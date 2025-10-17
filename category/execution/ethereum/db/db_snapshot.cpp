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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/endian.hpp> // little endian
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <ankerl/unordered_dense.h>
#include <quill/Quill.h>

#include <deque>
#include <limits>

inline constexpr unsigned MONAD_SNAPSHOT_SHARD_NIBBLES = 2;
inline constexpr unsigned MONAD_SNAPSHOT_SHARDS =
    1 << (MONAD_SNAPSHOT_SHARD_NIBBLES * 4);
static_assert(MONAD_SNAPSHOT_SHARDS == 256);

struct monad_db_snapshot_loader
{
    uint64_t block;
    monad::OnDiskMachine machine;
    monad::mpt::Db db;
    monad::mpt::Node::SharedPtr root;
    std::array<monad::byte_string, 256> eth_headers;
    std::deque<monad::hash256> hash_alloc;
    std::deque<monad::mpt::Update> update_alloc;
    std::array<
        ankerl::unordered_dense::segmented_map<uint64_t, monad::mpt::Update>,
        MONAD_SNAPSHOT_SHARDS>
        account_offset_to_update;
    monad::mpt::UpdateList state_updates;
    monad::mpt::UpdateList code_updates;
    uint64_t bytes_read;

    monad_db_snapshot_loader(
        uint64_t const block, char const *const *const dbname_paths,
        size_t const len, unsigned const sq_thread_cpu)
        : block{block}
        , db{machine,
             monad::mpt::OnDiskDbConfig{
                 .append = true,
                 .compaction = false,
                 .rd_buffers = 8192,
                 .wr_buffers = 32,
                 .uring_entries = 128,
                 .sq_thread_cpu =
                     sq_thread_cpu == std::numeric_limits<unsigned>::max()
                         ? std::nullopt
                         : std::make_optional(sq_thread_cpu),
                 .dbname_paths = {dbname_paths, dbname_paths + len}}}
        , bytes_read{0}
    {
    }
};

MONAD_ANONYMOUS_NAMESPACE_BEGIN

uint64_t get_shard(monad::mpt::NibblesView const path)
{
    uint64_t ret = 0;
    for (unsigned i = 0; i < MONAD_SNAPSHOT_SHARD_NIBBLES; ++i) {
        ret <<= 4;
        ret |= path.get(i);
    }
    MONAD_ASSERT(ret < MONAD_SNAPSHOT_SHARDS);
    return ret;
}

void monad_db_snapshot_loader_flush(monad_db_snapshot_loader *const loader)
{
    using namespace monad;
    using namespace monad::mpt;

    Update state_update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(loader->state_updates),
        .version = static_cast<int64_t>(loader->block)};
    Update code_update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(loader->code_updates),
        .version = static_cast<int64_t>(loader->block)};

    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);

    UpdateList finalized_updates;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(loader->block)};
    finalized_updates.push_front(finalized);

    loader->root = loader->db.upsert(
        std::move(loader->root),
        std::move(finalized_updates),
        loader->block,
        false,
        false);
    loader->hash_alloc.clear();
    loader->update_alloc.clear();
    for (auto &map : loader->account_offset_to_update) {
        map.clear();
    }
    loader->state_updates.clear();
    loader->code_updates.clear();
    loader->bytes_read = 0;
}

uint64_t monad_db_snapshot_loader_read_account(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    uint64_t const account_offset, monad::byte_string_view const accounts)
{
    using namespace monad;
    using namespace monad::mpt;
    byte_string_view bytes{accounts.substr(account_offset)};
    byte_string_view const before{bytes};
    auto const res = decode_account_db_raw(bytes);
    MONAD_ASSERT(res.has_value());
    auto const [address, account] = res.value();
    MONAD_ASSERT(address.size() == sizeof(Address));
    uint64_t const bytes_consumed = before.size() - bytes.size();
    auto const [it, success] =
        loader->account_offset_to_update.at(shard).emplace(
            account_offset,
            Update{
                .key = loader->hash_alloc.emplace_back(keccak256(address)),
                .value = before.substr(0, bytes_consumed),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(loader->block)});
    MONAD_ASSERT(success);
    loader->state_updates.push_front(it->second);
    loader->bytes_read += bytes_consumed;
    return bytes_consumed;
}

struct MonadSnapshotTraverseMachine : public monad::mpt::TraverseMachine
{
    unsigned char nibble;
    monad::mpt::Nibbles path;
    std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> &account_bytes_written;
    uint64_t account_offset;
    uint64_t (*write)(
        uint64_t shard, monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user);
    void *user;

    MonadSnapshotTraverseMachine(
        std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> &account_bytes_written,
        uint64_t (*write)(
            uint64_t shard, monad_snapshot_type, unsigned char const *bytes,
            size_t len, void *user),
        void *user)
        : nibble{monad::mpt::INVALID_BRANCH}
        , path{}
        , account_bytes_written{account_bytes_written}
        , account_offset{std::numeric_limits<uint64_t>::max()}
        , write(write)
        , user{user}
    {
    }

    virtual bool
    down(unsigned char const branch, monad::mpt::Node const &node) override
    {
        using namespace monad;
        using namespace monad::mpt;
        constexpr unsigned HASH_SIZE = KECCAK256_SIZE * 2;

        if (branch == INVALID_BRANCH) {
            MONAD_ASSERT(path.nibble_size() == 0);
            return true;
        }
        else if (path.nibble_size() == 0 && nibble == INVALID_BRANCH) {
            nibble = branch;
            return true;
        }
        MONAD_ASSERT(nibble == STATE_NIBBLE || nibble == CODE_NIBBLE);

        path = concat(NibblesView{path}, branch, node.path_nibble_view());

        if (!node.has_value()) {
            return true;
        }
        uint64_t const shard = get_shard(path);
        byte_string_view const val = node.value();
        if (nibble == CODE_NIBBLE) {
            MONAD_ASSERT(path.nibble_size() == HASH_SIZE);
            uint64_t const len = val.size();
            MONAD_ASSERT(
                write(
                    shard,
                    MONAD_SNAPSHOT_CODE,
                    reinterpret_cast<unsigned char const *>(&len),
                    sizeof(len),
                    user) == sizeof(len));
            MONAD_ASSERT(
                write(shard, MONAD_SNAPSHOT_CODE, val.data(), len, user) ==
                len);
        }
        else {
            MONAD_ASSERT(nibble == STATE_NIBBLE);
            monad_snapshot_type type;
            if (path.nibble_size() == HASH_SIZE) {
                type = MONAD_SNAPSHOT_ACCOUNT;
                account_offset = account_bytes_written.at(shard);
                account_bytes_written.at(shard) += val.size();
            }
            else {
                MONAD_ASSERT(path.nibble_size() == (HASH_SIZE * 2));
                type = MONAD_SNAPSHOT_STORAGE;
                MONAD_ASSERT(
                    write(
                        shard,
                        MONAD_SNAPSHOT_STORAGE,
                        reinterpret_cast<unsigned char const *>(
                            &account_offset),
                        sizeof(account_offset),
                        user) == sizeof(account_offset));
            }

            MONAD_ASSERT(
                write(shard, type, val.data(), val.size(), user) == val.size());
        }

        return true;
    }

    virtual void up(unsigned char const, monad::mpt::Node const &node) override
    {
        if (path.nibble_size() == 0) {
            nibble = monad::mpt::INVALID_BRANCH;
            return;
        }
        monad::mpt::NibblesView const view{path};
        path = view.substr(0, view.nibble_size() - 1 - node.path_nibbles_len());
    }

    virtual std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<MonadSnapshotTraverseMachine>(*this);
    }

    virtual bool
    should_visit(monad::mpt::Node const &, unsigned char const branch) override
    {
        using namespace monad;
        using namespace monad::mpt;
        if (path.nibble_size() == 0 && nibble == INVALID_BRANCH) {
            MONAD_ASSERT(branch != INVALID_BRANCH);
            return branch == STATE_NIBBLE || branch == CODE_NIBBLE;
        }
        return true;
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

// Directory Format
//   block number
//     shard
//       account    -> empty | leaf.value(), ...
//       storage    -> empty | [account_offset, leaf.value()], ...
//       code       -> empty | [size, code], ...
//       eth header -> empty | rlp(header)
bool monad_db_dump_snapshot(
    char const *const *const dbname_paths, size_t const len,
    unsigned const sq_thread_cpu, uint64_t const block,
    uint64_t (*write)(
        uint64_t shard, monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user),
    void *const user)
{
    using namespace monad;
    using namespace monad::mpt;

    ReadOnlyOnDiskDbConfig const config{
        .sq_thread_cpu = sq_thread_cpu != std::numeric_limits<unsigned>::max()
                             ? std::make_optional(sq_thread_cpu)
                             : std::nullopt,
        .dbname_paths = {dbname_paths, dbname_paths + len}};
    AsyncIOContext io_context{config};
    Db db{io_context};

    for (uint64_t b = block < 256 ? 0 : block - 255; b <= block; ++b) {
        auto const header_cursor_res = db.find(
            concat(FINALIZED_NIBBLE, NibblesView{block_header_nibbles}), b);
        if (!header_cursor_res.has_value()) {
            LOG_INFO(
                "Could not query block header {} from db -- {}",
                b,
                header_cursor_res.error().message().c_str());
            return false;
        }
        auto const header_view = header_cursor_res.value().node->value();
        MONAD_ASSERT(
            write(
                block - b,
                MONAD_SNAPSHOT_ETH_HEADER,
                header_view.data(),
                header_view.size(),
                user) == header_view.size());
    }

    auto const root = db.load_root_for_version(block);
    if (!root) {
        LOG_INFO("root not valid for block {}", block);
        return false;
    }
    auto const finalized_root_res =
        db.find(NodeCursor{root}, finalized_nibbles, block);
    if (!finalized_root_res.has_value()) {
        LOG_INFO("block {} not finalized", block);
        return false;
    }
    auto const &finalized_root = finalized_root_res.value();
    if (db.find(finalized_root, state_nibbles, block).has_error() ||
        db.find(finalized_root, code_nibbles, block).has_error()) {
        LOG_INFO("no code and/or state for block {}", block);
        return false;
    }

    std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> account_bytes_written{};
    MonadSnapshotTraverseMachine machine{account_bytes_written, write, user};
    bool const success = db.traverse(finalized_root, machine, block);
    if (!success) {
        LOG_INFO("db traverse for block {} unsuccessful", block);
    }
    return success;
}

monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t const block, char const *const *const dbname_paths,
    size_t const len, unsigned const sq_thread_cpu)
{
    auto *loader =
        new monad_db_snapshot_loader(block, dbname_paths, len, sq_thread_cpu);
    MONAD_ASSERT_PRINTF(
        loader->db.get_latest_version() == monad::mpt::INVALID_BLOCK_NUM,
        "database must be hard reset when loading snapshot");
    return loader;
}

void monad_db_snapshot_loader_load(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    unsigned char const *const eth_header, size_t const eth_header_len,
    unsigned char const *const account, size_t const account_len,
    unsigned char const *const storage, size_t const storage_len,
    unsigned char const *const code, size_t const code_len)
{
    using namespace monad;
    using namespace monad::mpt;
    constexpr size_t BYTES_READ_BEFORE_FLUSH = 10ull * 1024 * 1024 * 1024;
    MONAD_ASSERT(loader);
    if (account) {
        for (uint64_t account_offset = 0; account_offset != account_len;) {
            account_offset += monad_db_snapshot_loader_read_account(
                loader, shard, account_offset, {account, account_len});
            if (loader->bytes_read >= BYTES_READ_BEFORE_FLUSH) {
                monad_db_snapshot_loader_flush(loader);
            }
            MONAD_ASSERT(account_offset <= account_len);
        }
    }

    if (storage) {
        MONAD_ASSERT(account);
        byte_string_view storage_view{storage, storage_len};
        auto &account_offset_to_update =
            loader->account_offset_to_update.at(shard);
        while (!storage_view.empty()) {
            uint64_t const account_offset =
                unaligned_load<uint64_t>(storage_view.data());
            if (!account_offset_to_update.contains(account_offset)) {
                monad_db_snapshot_loader_read_account(
                    loader, shard, account_offset, {account, account_len});
            }
            storage_view.remove_prefix(sizeof(account_offset));
            byte_string_view const before{storage_view};
            auto const res = decode_storage_db_raw(storage_view);
            MONAD_ASSERT(res.has_value());
            auto &update = account_offset_to_update.at(account_offset);
            uint64_t const consumed = before.size() - storage_view.size();
            update.next.push_front(loader->update_alloc.emplace_back(Update{
                .key = loader->hash_alloc.emplace_back(
                    keccak256(to_bytes(res.value().first))),
                .value = before.substr(0, consumed),
                .next = UpdateList{},
                .version = static_cast<int64_t>(loader->block)}));
            loader->bytes_read += consumed;
            if (loader->bytes_read >= BYTES_READ_BEFORE_FLUSH) {
                monad_db_snapshot_loader_flush(loader);
            }
        }
    }

    if (code) {
        byte_string_view code_view{code, code_len};
        while (!code_view.empty()) {
            MONAD_ASSERT(code_view.size() >= sizeof(uint64_t));
            uint64_t const size = unaligned_load<uint64_t>(code_view.data());
            code_view.remove_prefix(sizeof(uint64_t));
            MONAD_ASSERT(code_view.size() >= size);
            byte_string_view const val = code_view.substr(0, size);
            loader->code_updates.push_front(
                loader->update_alloc.emplace_back(Update{
                    .key = loader->hash_alloc.emplace_back(keccak256(val)),
                    .value = val,
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(loader->block)}));
            code_view.remove_prefix(size);
            loader->bytes_read += sizeof(uint64_t) + size;
            if (loader->bytes_read >= BYTES_READ_BEFORE_FLUSH) {
                monad_db_snapshot_loader_flush(loader);
            }
        }
    }

    if (eth_header) {
        byte_string_view enc{eth_header, eth_header_len};
        auto const header = rlp::decode_block_header(enc);
        MONAD_ASSERT(header.has_value());
        MONAD_ASSERT(header.value().number == (loader->block - shard));
        // stash to upsert versions last
        loader->eth_headers.at(shard).assign(eth_header, eth_header_len);
    }
    monad_db_snapshot_loader_flush(loader);
}

void monad_db_snapshot_loader_destroy(monad_db_snapshot_loader *loader)
{
    using namespace monad;
    using namespace monad::mpt;
    for (size_t i = 0; i < loader->eth_headers.size(); ++i) {
        auto const &enc = loader->eth_headers[i];
        if (enc.empty()) {
            continue;
        }
        uint64_t const block = loader->block - i;
        Update block_header_update{
            .key = block_header_nibbles,
            .value = enc,
            .incarnation = true,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block)};
        UpdateList updates;
        updates.push_front(block_header_update);
        UpdateList finalized_updates;
        Update finalized{
            .key = finalized_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(updates),
            .version = static_cast<int64_t>(block)};
        finalized_updates.push_front(finalized);
        loader->db.upsert(
            loader->db.load_root_for_version(block),
            std::move(finalized_updates),
            block,
            false,
            false);
    }
    loader->db.update_finalized_version(loader->block);
    delete loader;
}
