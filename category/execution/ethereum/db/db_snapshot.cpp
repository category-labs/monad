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
#include <category/core/log.hpp>
#include <category/core/nibble.h>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_internal.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <ankerl/unordered_dense.h>

#include <deque>
#include <limits>
#include <memory>
#include <optional>

struct monad_db_snapshot_loader
{
    uint64_t block;
    monad::mpt::Db db;
    monad::mpt::Node::SharedPtr root;
    std::array<monad::byte_string, 256> eth_headers;

    monad_db_snapshot_loader(
        uint64_t const block, char const *const *const dbname_paths,
        size_t const len, unsigned const sq_thread_cpu,
        bool const load_to_secondary)
        : block{block}
        , db{open_target_db(
              dbname_paths, len, sq_thread_cpu, load_to_secondary)}
    {
    }

    bool page_encoded() const
    {
        return db.state_machine_type() == monad::mpt::state_machine_kind::monad;
    }

private:
    static monad::mpt::Db open_target_db(
        char const *const *const dbname_paths, size_t const len,
        unsigned const sq_thread_cpu, bool const load_to_secondary)
    {
        monad::mpt::Db primary{monad::mpt::OnDiskDbConfig{
            .append = true,
            .compaction = false,
            .rd_buffers = 8192,
            .wr_buffers = 32,
            .uring_entries = 128,
            .sq_thread_cpu =
                sq_thread_cpu == std::numeric_limits<unsigned>::max()
                    ? std::nullopt
                    : std::make_optional(sq_thread_cpu),
            .dbname_paths = {dbname_paths, dbname_paths + len}}};
        if (!load_to_secondary) {
            return primary;
        }
        auto secondary = primary.open_secondary_timeline();
        MONAD_ASSERT_PRINTF(
            secondary.has_value(),
            "secondary timeline is not active; activate it and stamp its "
            "state_machine_kind using monad-mpt tool before loading a snapshot "
            "into it");
        return std::move(*secondary);
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

class NibblePath
{
private:
    // 128 nibbles max: 64 (account hash) + 64 (storage hash)
    // Note: finalized and code/data nibbles are handled separately and not
    // stored in path
    std::array<unsigned char, 64> buffer_{};
    uint8_t length_{0};

public:
    void
    append(unsigned char const branch, monad::mpt::NibblesView const node_path)
    {
        using namespace monad::mpt;
        unsigned const src_nibbles = node_path.nibble_size();
        MONAD_ASSERT(length_ + 1 + src_nibbles <= buffer_.size() * 2);

        // Append branch nibble
        set_nibble(buffer_.data(), length_, branch);
        ++length_;

        if (src_nibbles == 0) {
            return;
        }

        for (unsigned i = 0; i < src_nibbles; ++i) {
            set_nibble(buffer_.data(), length_ + i, node_path.get(i));
        }
        length_ = static_cast<uint8_t>(length_ + src_nibbles);
    }

    void pop(uint8_t const nibble_count)
    {
        MONAD_ASSERT(length_ >= nibble_count);
        length_ -= nibble_count;
    }

    [[nodiscard]] monad::mpt::NibblesView view() const
    {
        return monad::mpt::NibblesView(0, length_, buffer_.data());
    }

    [[nodiscard]] uint8_t length() const
    {
        return length_;
    }
};

struct MonadSnapshotTraverseMachine : public monad::mpt::TraverseMachine
{
    unsigned char nibble;
    NibblePath path;
    std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> &account_bytes_written;
    uint64_t account_offset;
    uint64_t (*write)(
        uint64_t shard, monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user);
    void *user;
    uint64_t total_shards;
    uint64_t shard_number;
    // Source db is page-encoded: storage leaves hold encoded pages rather than
    // single slots, so they are expanded to slot-format entries on dump.
    bool page_encoded;

    MonadSnapshotTraverseMachine(
        std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> &account_bytes_written,
        uint64_t (*write)(
            uint64_t shard, monad_snapshot_type, unsigned char const *bytes,
            size_t len, void *user),
        void *const user, uint64_t const total_shards,
        uint64_t const shard_number, bool const page_encoded)
        : nibble{monad::mpt::INVALID_BRANCH}
        , path{}
        , account_bytes_written{account_bytes_written}
        , account_offset{std::numeric_limits<uint64_t>::max()}
        , write(write)
        , user{user}
        , total_shards{total_shards}
        , shard_number{shard_number}
        , page_encoded{page_encoded}
    {
    }

    virtual bool
    down(unsigned char const branch, monad::mpt::Node const &node) override
    {
        using namespace monad;
        using namespace monad::mpt;
        constexpr unsigned HASH_SIZE = KECCAK256_SIZE * 2;

        if (branch == INVALID_BRANCH) {
            MONAD_ASSERT(path.length() == 0);
            return true;
        }
        else if (path.length() == 0 && nibble == INVALID_BRANCH) {
            nibble = branch;
            return true;
        }
        MONAD_ASSERT(nibble == STATE_NIBBLE || nibble == CODE_NIBBLE);

        path.append(branch, node.path_nibble_view());

        // Path not long enough to determine shard yet, continue traversing
        if (path.length() < MONAD_SNAPSHOT_SHARD_NIBBLES) {
            return true;
        }

        uint64_t const shard = get_shard(path.view());

        // Return false to skip entire subtree since all descendants have same
        // shard
        if (shard % total_shards != shard_number) {
            return false;
        }

        // If intermediate node (no value), continue traversing deeper
        if (!node.has_value()) {
            return true;
        }

        byte_string_view const val = node.value();
        if (nibble == CODE_NIBBLE) {
            MONAD_ASSERT(path.length() == HASH_SIZE);
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
            if (path.length() == HASH_SIZE) {
                account_offset = account_bytes_written.at(shard);
                account_bytes_written.at(shard) += val.size();
                MONAD_ASSERT(
                    write(
                        shard,
                        MONAD_SNAPSHOT_ACCOUNT,
                        val.data(),
                        val.size(),
                        user) == val.size());
            }
            else {
                MONAD_ASSERT(path.length() == (HASH_SIZE * 2));
                // Emit one slot-format storage entry, prefixed with the owning
                // account's offset so the loader can re-link it.
                auto const emit_slot = [&](byte_string_view const entry) {
                    MONAD_ASSERT(
                        write(
                            shard,
                            MONAD_SNAPSHOT_STORAGE,
                            reinterpret_cast<unsigned char const *>(
                                &account_offset),
                            sizeof(account_offset),
                            user) == sizeof(account_offset));
                    MONAD_ASSERT(
                        write(
                            shard,
                            MONAD_SNAPSHOT_STORAGE,
                            entry.data(),
                            entry.size(),
                            user) == entry.size());
                };
                if (page_encoded) {
                    // Source db is page-encoded: expand the storage leaf into
                    // one slot-encoded entry per non-zero slot so the dumped
                    // snapshot stays slot-granular and loads unchanged.
                    auto const decoded =
                        decode_storage_page_leaf(byte_string_view{val});
                    MONAD_ASSERT(decoded.has_value());
                    for (auto const [slot_key, slot_val] :
                         decoded.value().slots()) {
                        emit_slot(encode_storage_db(slot_key, slot_val));
                    }
                }
                else {
                    emit_slot(val);
                }
            }
        }

        return true;
    }

    virtual void up(unsigned char const, monad::mpt::Node const &node) override
    {
        if (path.length() == 0) {
            nibble = monad::mpt::INVALID_BRANCH;
            return;
        }
        // Remove branch nibble + node path nibbles that were added in down()
        path.pop(static_cast<uint8_t>(1 + node.path_nibbles_len()));
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
        if (path.length() == 0 && nibble == INVALID_BRANCH) {
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
    void *const user, unsigned const dump_concurrency_limit,
    uint64_t const total_shards, uint64_t const shard_number,
    bool const dump_from_secondary)
{
    using namespace monad;
    using namespace monad::mpt;

    MONAD_ASSERT_PRINTF(
        total_shards >= 1, "total_shards must be >= 1, got %lu", total_shards);
    MONAD_ASSERT_PRINTF(
        shard_number < total_shards,
        "shard_number (%lu) must be < total_shards (%lu)",
        shard_number,
        total_shards);

    // Set all queue sizes to dump_concurrency_limit to avoid double queuing
    ReadOnlyOnDiskDbConfig const config{
        .rd_buffers = dump_concurrency_limit,
        .uring_entries = dump_concurrency_limit,
        .sq_thread_cpu = sq_thread_cpu != std::numeric_limits<unsigned>::max()
                             ? std::make_optional(sq_thread_cpu)
                             : std::nullopt,
        .dbname_paths = {dbname_paths, dbname_paths + len},
        .concurrent_read_io_limit = dump_concurrency_limit};
    AsyncIOContext io_context{config};
    Db db{
        io_context,
        dump_from_secondary ? timeline_id::secondary : timeline_id::primary};

    for (uint64_t b = block < 256 ? 0 : block - 255; b <= block; ++b) {
        uint64_t const header_shard = block - b;
        if (header_shard % total_shards != shard_number) {
            continue;
        }

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
                header_shard,
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
    MonadSnapshotTraverseMachine machine{
        account_bytes_written,
        write,
        user,
        total_shards,
        shard_number,
        db.state_machine_type() == state_machine_kind::monad};
    bool const success =
        db.traverse(finalized_root, machine, block, dump_concurrency_limit);
    if (!success) {
        LOG_INFO("db traverse for block {} unsuccessful", block);
    }
    return success;
}

// Loads the standard slot-encoded snapshot (the format produced by
// monad_db_dump_snapshot against a slot db) into one timeline:
//   * load_to_secondary == false: the primary timeline.
//   * load_to_secondary == true:  an already-activated secondary timeline.
// The target's storage encoding is derived from its persisted
// state_machine_kind; a page-encoded target converts slot leaves to page
// leaves on the fly. The target's kind must already be stamped on disk.
monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t const block, char const *const *const dbname_paths,
    size_t const len, unsigned const sq_thread_cpu,
    bool const load_to_secondary)
{
    // The metadata-driven Db ctor and open_secondary_timeline() resolve the
    // persisted kind through the registry, so both factories must be present.
    monad::register_ethereum_state_machines();
    monad::register_monad_state_machines();
    auto *loader = new monad_db_snapshot_loader(
        block, dbname_paths, len, sq_thread_cpu, load_to_secondary);
    MONAD_ASSERT(
        loader->db.get_latest_version() == monad::mpt::INVALID_BLOCK_NUM,
        "database must be empty when loading snapshot");
    return loader;
}

void fill_prepared_shard(
    monad::PreparedShard &ps_ref, uint64_t const shard, uint64_t const block,
    bool const page_encoded, monad::byte_string_view const eth_header,
    monad::byte_string_view const account,
    monad::byte_string_view const storage, monad::byte_string_view const code)
{
    using namespace monad;
    using namespace monad::mpt;

    PreparedShard *const ps = &ps_ref;
    ps->shard = shard;

    auto const read_account = [&](uint64_t const account_offset) -> uint64_t {
        byte_string_view bytes{account.substr(account_offset)};
        byte_string_view const before{bytes};
        auto const res = decode_account_db_raw(bytes);
        MONAD_ASSERT(res.has_value());
        auto const [address, acct] = res.value();
        MONAD_ASSERT(address.size() == sizeof(Address));
        uint64_t const consumed = before.size() - bytes.size();
        auto const [it, ok] = ps->account_updates.emplace(
            account_offset,
            Update{
                .key = ps->hash_alloc.emplace_back(keccak256(address)),
                .value = before.substr(0, consumed),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block)});
        MONAD_ASSERT(ok);
        ps->state_updates.push_front(it->second);
        return consumed;
    };

    if (!account.empty()) {
        for (uint64_t off = 0; off != account.size();) {
            off += read_account(off);
            MONAD_ASSERT(off <= account.size());
        }
    }

    // Page mode: local accumulator drained into page-leaf Updates at the end.
    ankerl::unordered_dense::segmented_map<
        uint64_t,
        ankerl::unordered_dense::map<bytes32_t, storage_page_t>>
        page_accumulator;

    if (!storage.empty()) {
        MONAD_ASSERT(!account.empty());
        byte_string_view sv{storage};
        while (!sv.empty()) {
            uint64_t const account_offset = unaligned_load<uint64_t>(sv.data());
            if (!ps->account_updates.contains(account_offset)) {
                read_account(account_offset);
            }
            sv.remove_prefix(sizeof(account_offset));
            byte_string_view const before{sv}; // capture BEFORE decode
            // decode_storage_db_raw advances sv and tolerates trailing bytes,
            // since the storage stream concatenates multiple
            // [account_offset, leaf.value()] entries.
            auto const res = decode_storage_db_raw(sv);
            MONAD_ASSERT(res.has_value());
            uint64_t const consumed = before.size() - sv.size();
            if (page_encoded) {
                bytes32_t const slot_key = to_bytes(res.value().first);
                bytes32_t const slot_val = to_bytes(res.value().second);
                page_accumulator[account_offset][compute_page_key(slot_key)]
                    .set(compute_slot_offset(slot_key), slot_val);
            }
            else {
                // The leaf value must be the exact encoded bytes from the input
                // stream (a view into `storage`), not a re-encode, which could
                // differ and change the root.
                auto &upd = ps->account_updates.at(account_offset);
                upd.next.push_front(ps->update_alloc.emplace_back(Update{
                    .key = ps->hash_alloc.emplace_back(
                        keccak256(to_bytes(res.value().first))),
                    .value = before.substr(0, consumed),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(block)}));
            }
        }
    }

    // Drain the page accumulator into page-leaf Updates. Each page becomes one
    // Update keyed by keccak256(page_key), valued with the encoded page (or a
    // deletion when empty). All slots sharing a page_key are in this single
    // shard's accumulator, so no cross-shard page merge is possible.
    if (page_encoded) {
        for (auto &[account_offset, pages] : page_accumulator) {
            auto &account_update = ps->account_updates.at(account_offset);
            for (auto const &[page_key, page] : pages) {
                std::optional<byte_string_view> value;
                if (!page.is_empty()) {
                    value = byte_string_view{ps->bytes_alloc.emplace_back(
                        encode_storage_page_db(page_key, page))};
                }
                account_update.next.push_front(
                    ps->update_alloc.emplace_back(Update{
                        .key = ps->hash_alloc.emplace_back(keccak256(
                            {page_key.bytes, sizeof(page_key.bytes)})),
                        .value = value,
                        .incarnation = false,
                        .next = UpdateList{},
                        .version = static_cast<int64_t>(block)}));
            }
        }
    }

    if (!code.empty()) {
        byte_string_view cv{code};
        while (!cv.empty()) {
            MONAD_ASSERT(cv.size() >= sizeof(uint64_t));
            uint64_t const size = unaligned_load<uint64_t>(cv.data());
            cv.remove_prefix(sizeof(uint64_t));
            MONAD_ASSERT(cv.size() >= size);
            byte_string_view const val = cv.substr(0, size);
            ps->code_updates.push_front(ps->update_alloc.emplace_back(Update{
                .key = ps->hash_alloc.emplace_back(keccak256(val)),
                .value = val,
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block)}));
            cv.remove_prefix(size);
        }
    }

    if (!eth_header.empty()) {
        byte_string_view enc{eth_header};
        auto const header = rlp::decode_block_header(enc);
        MONAD_ASSERT(header.has_value());
        MONAD_ASSERT(header.value().number == (block - shard));
        ps->eth_header.assign(eth_header.begin(), eth_header.end());
    }
}

void commit_prepared(
    monad_db_snapshot_loader *const loader,
    std::unique_ptr<monad::PreparedShard> ps)
{
    using namespace monad;
    using namespace monad::mpt;

    Update state_update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(ps->state_updates),
        .version = static_cast<int64_t>(loader->block)};
    Update code_update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(ps->code_updates),
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

    if (!ps->eth_header.empty()) {
        loader->eth_headers.at(ps->shard) = std::move(ps->eth_header);
    }
    // ps (and its mmaps + allocs) freed here, after upsert copied the values.
}

bool snapshot_loader_page_encoded(monad_db_snapshot_loader const *const loader)
{
    return loader->page_encoded();
}

void monad_db_snapshot_loader_load(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    unsigned char const *const eth_header, size_t const eth_header_len,
    unsigned char const *const account, size_t const account_len,
    unsigned char const *const storage, size_t const storage_len,
    unsigned char const *const code, size_t const code_len)
{
    using monad::byte_string_view;
    MONAD_ASSERT(loader);
    auto const view = [](unsigned char const *const p, size_t const n) {
        return p ? byte_string_view{p, n} : byte_string_view{};
    };
    auto ps = std::make_unique<monad::PreparedShard>();
    fill_prepared_shard(
        *ps,
        shard,
        loader->block,
        loader->page_encoded(),
        view(eth_header, eth_header_len),
        view(account, account_len),
        view(storage, storage_len),
        view(code, code_len));
    commit_prepared(loader, std::move(ps));
}

void monad_db_snapshot_loader_destroy(monad_db_snapshot_loader *const loader)
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
