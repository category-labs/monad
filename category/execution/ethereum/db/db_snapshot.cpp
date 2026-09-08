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
    std::deque<monad_hash256> hash_alloc;
    std::deque<monad::mpt::Update> update_alloc;
    std::deque<monad::byte_string> bytes_alloc;
    std::array<
        ankerl::unordered_dense::segmented_map<uint64_t, monad::mpt::Update>,
        MONAD_SNAPSHOT_SHARDS>
        account_offset_to_update;
    // Per-shard page accumulator, used only for a page-encoded target whose
    // input stream groups slots more finely than a target page, so that pages
    // cannot be closed as they are read. Maps account_offset -> (page_key ->
    // assembled storage_page_t).
    std::array<
        ankerl::unordered_dense::segmented_map<
            uint64_t, ankerl::unordered_dense::map<
                          monad::bytes32_t, monad::storage_page_t>>,
        MONAD_SNAPSHOT_SHARDS>
        page_accumulator;
    monad::mpt::UpdateList state_updates;
    monad::mpt::UpdateList code_updates;
    uint64_t bytes_read;
    uint64_t flush_bytes;

    monad_db_snapshot_loader(
        uint64_t const block, char const *const *const dbname_paths,
        size_t const len, unsigned const sq_thread_cpu,
        bool const load_to_secondary)
        : block{block}
        , db{open_target_db(
              dbname_paths, len, sq_thread_cpu, load_to_secondary)}
        , bytes_read{0}
        , flush_bytes{MONAD_SNAPSHOT_DEFAULT_FLUSH_BYTES}
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

// Drain whatever the accumulator holds into per-account `next` lists; it is
// populated only when pages cannot be closed as the stream is read, and empty
// otherwise. Each page becomes one Update keyed by keccak256(page_key)
// with value encode_storage_page_db(page_key, page) (or std::nullopt if the
// page is empty so the entry is a deletion). The encoded byte_strings are
// kept alive in loader->bytes_alloc until the upsert completes; the Update
// nodes are kept in loader->update_alloc for the same reason.
void monad_db_snapshot_loader_finalize_pages(
    monad_db_snapshot_loader *const loader)
{
    using namespace monad;
    using namespace monad::mpt;
    if (!loader->page_encoded()) {
        return;
    }
    for (size_t shard = 0; shard < MONAD_SNAPSHOT_SHARDS; ++shard) {
        auto &shard_pages = loader->page_accumulator.at(shard);
        if (shard_pages.empty()) {
            continue;
        }
        auto &shard_accounts = loader->account_offset_to_update.at(shard);
        for (auto &[account_offset, pages] : shard_pages) {
            auto &account_update = shard_accounts.at(account_offset);
            for (auto const &[page_key, page] : pages) {
                bool const is_empty = page.is_empty();
                std::optional<byte_string_view> value;
                if (!is_empty) {
                    value = byte_string_view{loader->bytes_alloc.emplace_back(
                        encode_storage_page_db(page_key, page))};
                }
                account_update.next.push_front(
                    loader->update_alloc.emplace_back(Update{
                        .key = loader->hash_alloc.emplace_back(keccak256(
                            {page_key.bytes, sizeof(page_key.bytes)})),
                        .value = value,
                        .incarnation = false,
                        .next = UpdateList{},
                        .version = static_cast<int64_t>(loader->block)}));
            }
        }
        shard_pages.clear();
    }
}

void monad_db_snapshot_loader_flush(monad_db_snapshot_loader *const loader)
{
    using namespace monad;
    using namespace monad::mpt;

    monad_db_snapshot_loader_finalize_pages(loader);

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
    loader->bytes_alloc.clear();
    for (auto &map : loader->account_offset_to_update) {
        map.clear();
    }
    for (auto &map : loader->page_accumulator) {
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

struct StreamFormat
{
    // Whether a storage stream's records carry a group prefix. False for a
    // version 1 stream and for one written before headers existed, both of
    // which hold one slot entry per record.
    bool grouped;
    // Zero unless the stream groups storage slots more coarsely than one slot
    // at a time.
    uint8_t group_key_shift;
};

// Consume the stream header if there is one, leaving `stream` at its first
// record.
StreamFormat read_stream_header(
    monad::byte_string_view &stream, monad_snapshot_type const kind)
{
    using namespace monad;
    if (stream.size() < sizeof(monad_snapshot_stream_header)) {
        return {.grouped = false, .group_key_shift = 0};
    }
    auto const header =
        unaligned_load<monad_snapshot_stream_header>(stream.data());
    if (header.magic != MONAD_SNAPSHOT_STREAM_MAGIC) {
        return {.grouped = false, .group_key_shift = 0};
    }
    // A legacy stream can hold the guard byte by chance, but not the magic, so
    // past the magic a bad guard is corruption rather than an older layout and
    // must not silently bypass the version and kind checks below.
    MONAD_ASSERT_PRINTF(
        header.guard == MONAD_SNAPSHOT_STREAM_GUARD,
        "snapshot stream opens with the header magic but guard 0x%02x "
        "(expected 0x%02x)",
        header.guard,
        MONAD_SNAPSHOT_STREAM_GUARD);
    MONAD_ASSERT_PRINTF(
        header.version == MONAD_SNAPSHOT_STREAM_VERSION ||
            header.version == MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED,
        "snapshot stream version %u is not supported (expected %u or %u)",
        header.version,
        MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED,
        MONAD_SNAPSHOT_STREAM_VERSION);
    MONAD_ASSERT_PRINTF(
        header.kind == kind,
        "snapshot stream holds kind %u where kind %u was expected",
        header.kind,
        static_cast<unsigned>(kind));
    stream.remove_prefix(sizeof(header));
    if (header.version == MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED) {
        return {.grouped = false, .group_key_shift = 0};
    }
    return {.grouped = true, .group_key_shift = header.group_key_shift};
}

// Byte length of the encode_storage_db entry at the head of `stream`, which is
// the whole group of an ungrouped stream.
size_t storage_entry_length(monad::byte_string_view const stream)
{
    monad::byte_string_view rest{stream};
    auto const res = monad::decode_storage_db_raw(rest);
    MONAD_ASSERT(res.has_value());
    return stream.size() - rest.size();
}

void emit_slot_updates(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    uint64_t const account_offset, monad::byte_string_view payload)
{
    using namespace monad;
    using namespace monad::mpt;
    auto &account_update =
        loader->account_offset_to_update.at(shard).at(account_offset);
    while (!payload.empty()) {
        byte_string_view const before{payload};
        auto const res = decode_storage_db_raw(payload);
        MONAD_ASSERT(res.has_value());
        account_update.next.push_front(loader->update_alloc.emplace_back(Update{
            .key = loader->hash_alloc.emplace_back(
                keccak256(to_bytes(res.value().first))),
            .value = before.substr(0, before.size() - payload.size()),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(loader->block)}));
    }
}

// Assemble the target pages held by one closed group and push them onto the
// owning account. A leaf's slots arrive in ascending key order, so a page is
// complete as soon as the page key changes. Plural because a group_key_shift
// coarser than the target's page key is legal and would put several pages in
// one group; no dumper emits one, as source and target shift are the same
// constant.
void emit_page_updates(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    uint64_t const account_offset, monad::byte_string_view payload)
{
    using namespace monad;
    using namespace monad::mpt;
    auto &account_update =
        loader->account_offset_to_update.at(shard).at(account_offset);
    storage_page_t page;
    bytes32_t page_key{};
    bool have_page = false;
    auto const emit = [&] {
        // Dropped rather than written as a deletion the way the accumulator
        // path does, which is equivalent only because the target starts empty.
        if (page.is_empty()) {
            return;
        }
        account_update.next.push_front(loader->update_alloc.emplace_back(Update{
            .key = loader->hash_alloc.emplace_back(
                keccak256({page_key.bytes, sizeof(page_key.bytes)})),
            .value = byte_string_view{loader->bytes_alloc.emplace_back(
                encode_storage_page_db(page_key, page))},
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(loader->block)}));
    };
    while (!payload.empty()) {
        auto const res = decode_storage_db_raw(payload);
        MONAD_ASSERT(res.has_value());
        bytes32_t const slot_key = to_bytes(res.value().first);
        bytes32_t const key = compute_page_key(slot_key);
        if (!have_page) {
            page_key = key;
            have_page = true;
        }
        else if (key != page_key) {
            // Ascending order is what makes a page complete here. Were the
            // group unordered, one page key could recur after being emitted and
            // the second Update would overwrite the first (upsert is
            // set-not-merge), silently dropping slots.
            MONAD_ASSERT(key > page_key);
            emit();
            page = storage_page_t{};
            page_key = key;
        }
        page.set(compute_slot_offset(slot_key), to_bytes(res.value().second));
    }
    emit();
}

// Merge the group's slots into the whole-shard accumulator, for a stream whose
// groups do not cover a target page.
void accumulate_page_slots(
    monad_db_snapshot_loader *const loader, uint64_t const shard,
    uint64_t const account_offset, monad::byte_string_view payload)
{
    using namespace monad;
    auto &account_pages = loader->page_accumulator.at(shard)[account_offset];
    while (!payload.empty()) {
        auto const res = decode_storage_db_raw(payload);
        MONAD_ASSERT(res.has_value());
        bytes32_t const slot_key = to_bytes(res.value().first);
        account_pages[compute_page_key(slot_key)].set(
            compute_slot_offset(slot_key), to_bytes(res.value().second));
    }
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

using SnapshotWriteFn = uint64_t (*)(
    uint64_t shard, monad_snapshot_type, unsigned char const *bytes, size_t len,
    void *user);

// Writes the records of every stream of one dump, and is shared by every clone
// of the traverse machine as well as by the eth-header writes outside it. The
// parallel traverse is single threaded (see Db::traverse), so one scratch
// buffer serves all clones: a storage group is built and written within a
// single down() call.
//
// Every record goes through here so that no stream can be opened without its
// header: a stream missing one is indistinguishable from a stream written
// before headers existed, so it would load without complaint.
class SnapshotStreamWriter
{
    SnapshotWriteFn const write_;
    void *const user_;
    // Group key shift stamped on a storage stream's header; zero for a
    // slot-encoded source, whose groups hold one slot each.
    uint8_t const storage_group_key_shift_;
    std::array<
        std::array<bool, MONAD_SNAPSHOT_FILES_PER_SHARD>, MONAD_SNAPSHOT_SHARDS>
        header_written_{};
    // Length of each shard's account stream counted from its first record, so
    // that the offsets it hands out do not shift when a header is present.
    std::array<uint64_t, MONAD_SNAPSHOT_SHARDS> account_bytes_written_{};
    monad::byte_string group_buffer_;

    // Written lazily so that a kind a shard has no records for leaves a
    // zero-length stream rather than a header-only one.
    void write_stream_header_once(
        uint64_t const shard, monad_snapshot_type const kind)
    {
        auto &written = header_written_.at(shard).at(kind);
        if (written) {
            return;
        }
        monad_snapshot_stream_header const header{
            .magic = MONAD_SNAPSHOT_STREAM_MAGIC,
            .version = MONAD_SNAPSHOT_STREAM_VERSION,
            .kind = static_cast<uint8_t>(kind),
            .group_key_shift = kind == MONAD_SNAPSHOT_STORAGE
                                   ? storage_group_key_shift_
                                   : uint8_t{0},
            .guard = MONAD_SNAPSHOT_STREAM_GUARD};
        std::array<unsigned char, sizeof(header)> bytes;
        monad::unaligned_store(bytes.data(), header);
        MONAD_ASSERT(
            write_(shard, kind, bytes.data(), bytes.size(), user_) ==
            bytes.size());
        written = true;
    }

public:
    SnapshotStreamWriter(
        SnapshotWriteFn const write, void *const user,
        uint8_t const storage_group_key_shift)
        : write_{write}
        , user_{user}
        , storage_group_key_shift_{storage_group_key_shift}
    {
    }

    SnapshotStreamWriter(SnapshotStreamWriter const &) = delete;

    void write_record(
        uint64_t const shard, monad_snapshot_type const kind,
        unsigned char const *const bytes, size_t const len)
    {
        write_stream_header_once(shard, kind);
        MONAD_ASSERT(write_(shard, kind, bytes, len, user_) == len);
    }

    // Appends one account record, returning the offset it occupies in the
    // shard's account stream, which is how a storage group names its account.
    uint64_t write_account_record(
        uint64_t const shard, unsigned char const *const bytes,
        size_t const len)
    {
        uint64_t const offset = account_bytes_written_.at(shard);
        account_bytes_written_.at(shard) += len;
        write_record(shard, MONAD_SNAPSHOT_ACCOUNT, bytes, len);
        return offset;
    }

    // Appends one storage group, prefixed with `account_offset` and its payload
    // length. `append_payload` appends the group's slot-encoded entries; a
    // group whose payload stays empty writes nothing.
    template <typename AppendPayload>
    void write_storage_group(
        uint64_t const shard, uint64_t const account_offset,
        AppendPayload const &append_payload)
    {
        constexpr size_t prefix = MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE;
        group_buffer_.clear();
        group_buffer_.resize(prefix);
        append_payload(group_buffer_);

        size_t const payload_len = group_buffer_.size() - prefix;
        if (payload_len == 0) {
            return;
        }
        MONAD_ASSERT(payload_len <= std::numeric_limits<uint32_t>::max());

        unsigned char *const cursor = group_buffer_.data();
        monad::unaligned_store(cursor, account_offset);
        monad::unaligned_store(
            cursor + sizeof(account_offset),
            static_cast<uint32_t>(payload_len));
        write_record(
            shard,
            MONAD_SNAPSHOT_STORAGE,
            group_buffer_.data(),
            group_buffer_.size());
    }
};

struct MonadSnapshotTraverseMachine : public monad::mpt::TraverseMachine
{
    unsigned char nibble;
    NibblePath path;
    SnapshotStreamWriter &writer;
    uint64_t account_offset;
    uint64_t total_shards;
    uint64_t shard_number;
    // Source db is page-encoded: storage leaves hold encoded pages rather than
    // single slots, so they are expanded to slot-format entries on dump.
    bool page_encoded;

    MonadSnapshotTraverseMachine(
        SnapshotStreamWriter &writer, uint64_t const total_shards,
        uint64_t const shard_number, bool const page_encoded)
        : nibble{monad::mpt::INVALID_BRANCH}
        , path{}
        , writer{writer}
        , account_offset{std::numeric_limits<uint64_t>::max()}
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
            writer.write_record(
                shard,
                MONAD_SNAPSHOT_CODE,
                reinterpret_cast<unsigned char const *>(&len),
                sizeof(len));
            writer.write_record(
                shard, MONAD_SNAPSHOT_CODE, val.data(), val.size());
        }
        else {
            MONAD_ASSERT(nibble == STATE_NIBBLE);
            if (path.length() == HASH_SIZE) {
                account_offset =
                    writer.write_account_record(shard, val.data(), val.size());
            }
            else {
                MONAD_ASSERT(path.length() == (HASH_SIZE * 2));
                write_storage_group(shard, val);
            }
        }

        return true;
    }

    // Turn one storage leaf into one group of the shard's storage stream. The
    // slots of a page-encoded leaf are expanded to slot-encoded entries so the
    // format stays slot-granular, but they stay together in one group, which is
    // what lets the loader rebuild a page without holding the whole shard.
    void
    write_storage_group(uint64_t const shard, monad::byte_string_view const val)
    {
        using namespace monad;

        MONAD_ASSERT(account_offset != std::numeric_limits<uint64_t>::max());

        writer.write_storage_group(
            shard, account_offset, [&](byte_string &payload) {
                if (!page_encoded) {
                    payload += val;
                    return;
                }
                auto const decoded = decode_storage_page_leaf(val);
                MONAD_ASSERT(decoded.has_value());
                for (auto const [slot_key, slot_val] :
                     decoded.value().slots()) {
                    payload += encode_storage_db(slot_key, slot_val);
                }
            });
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
//       account
//       storage
//       code
//       eth_header
// Each file holds one stream, empty or in the layout db_snapshot.h describes.
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

    bool const page_encoded =
        db.state_machine_type() == state_machine_kind::monad;
    SnapshotStreamWriter writer{
        write,
        user,
        page_encoded ? static_cast<uint8_t>(storage_page_t::PAGE_KEY_SHIFT)
                     : uint8_t{0}};
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
        writer.write_record(
            header_shard,
            MONAD_SNAPSHOT_ETH_HEADER,
            header_view.data(),
            header_view.size());
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

    MonadSnapshotTraverseMachine machine{
        writer, total_shards, shard_number, page_encoded};
    bool const success =
        db.traverse(finalized_root, machine, block, dump_concurrency_limit);
    if (!success) {
        LOG_INFO("db traverse for block {} unsuccessful", block);
    }
    return success;
}

// Loads a snapshot (the slot-granular format produced by
// monad_db_dump_snapshot) into one timeline:
//   * load_to_secondary == false: the primary timeline.
//   * load_to_secondary == true:  an already-activated secondary timeline.
// The target's storage encoding is derived from its persisted
// state_machine_kind; a page-encoded target assembles page leaves from the slot
// entries on the fly. The target's kind must already be stamped on disk.
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

void monad_db_snapshot_loader_set_flush_bytes(
    monad_db_snapshot_loader *const loader, uint64_t const bytes)
{
    MONAD_ASSERT(loader);
    loader->flush_bytes = bytes;
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
    MONAD_ASSERT(loader);
    // Account offsets index from the first account record, so the storage loop
    // below must resolve them against this header-stripped view rather than the
    // raw buffer.
    byte_string_view accounts{};
    if (account) {
        accounts = byte_string_view{account, account_len};
        read_stream_header(accounts, MONAD_SNAPSHOT_ACCOUNT);
        for (uint64_t account_offset = 0; account_offset != accounts.size();) {
            account_offset += monad_db_snapshot_loader_read_account(
                loader, shard, account_offset, accounts);
            if (loader->bytes_read >= loader->flush_bytes) {
                monad_db_snapshot_loader_flush(loader);
            }
            MONAD_ASSERT(account_offset <= accounts.size());
        }
    }

    if (storage) {
        MONAD_ASSERT(account);
        byte_string_view storage_view{storage, storage_len};
        auto const [grouped, group_key_shift] =
            read_stream_header(storage_view, MONAD_SNAPSHOT_STORAGE);
        // A group closes a target page only if its key is at least as coarse;
        // otherwise a page's slots span groups that arrive in any order, so
        // nothing can be written until the whole shard has been read.
        bool const close_pages_per_group =
            group_key_shift >= storage_page_t::PAGE_KEY_SHIFT;
        bool const can_flush = !loader->page_encoded() || close_pages_per_group;
        auto const &account_offset_to_update =
            loader->account_offset_to_update.at(shard);
        while (!storage_view.empty()) {
            MONAD_ASSERT(
                storage_view.size() >
                (grouped ? MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE
                         : sizeof(uint64_t)));
            uint64_t const account_offset =
                unaligned_load<uint64_t>(storage_view.data());
            size_t payload_len;
            if (grouped) {
                payload_len = unaligned_load<uint32_t>(
                    storage_view.data() + sizeof(account_offset));
                storage_view.remove_prefix(
                    MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE);
            }
            else {
                storage_view.remove_prefix(sizeof(account_offset));
                payload_len = storage_entry_length(storage_view);
            }
            // A dump never writes an empty group, so one here would silently
            // drop the slots the reader expected to find in it.
            MONAD_ASSERT(payload_len != 0);
            MONAD_ASSERT(payload_len <= storage_view.size());
            byte_string_view const payload{storage_view.substr(0, payload_len)};
            storage_view.remove_prefix(payload_len);

            if (!account_offset_to_update.contains(account_offset)) {
                monad_db_snapshot_loader_read_account(
                    loader, shard, account_offset, accounts);
            }
            if (!loader->page_encoded()) {
                emit_slot_updates(loader, shard, account_offset, payload);
            }
            else if (close_pages_per_group) {
                emit_page_updates(loader, shard, account_offset, payload);
            }
            else {
                accumulate_page_slots(loader, shard, account_offset, payload);
            }

            loader->bytes_read +=
                (grouped ? MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE
                         : sizeof(account_offset)) +
                payload_len;
            if (can_flush && loader->bytes_read >= loader->flush_bytes) {
                monad_db_snapshot_loader_flush(loader);
            }
        }
    }

    if (code) {
        byte_string_view code_view{code, code_len};
        read_stream_header(code_view, MONAD_SNAPSHOT_CODE);
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
            if (loader->bytes_read >= loader->flush_bytes) {
                monad_db_snapshot_loader_flush(loader);
            }
        }
    }

    if (eth_header) {
        byte_string_view enc{eth_header, eth_header_len};
        read_stream_header(enc, MONAD_SNAPSHOT_ETH_HEADER);
        byte_string_view const rlp_header{enc};
        auto const header = rlp::decode_block_header(enc);
        MONAD_ASSERT(header.has_value());
        MONAD_ASSERT(header.value().number == (loader->block - shard));
        // stash to upsert versions last
        loader->eth_headers.at(shard).assign(rlp_header);
    }
    monad_db_snapshot_loader_flush(loader);
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
