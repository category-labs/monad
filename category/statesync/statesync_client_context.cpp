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
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/update.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <ankerl/unordered_dense.h>

#include <deque>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::optional<unsigned> const sq_thread_cpu, unsigned const wr_buffers,
    monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
    : db{mpt::OnDiskDbConfig{
          .append = true,
          .compaction = false,
          .rewind_to_latest_finalized = true,
          .rd_buffers = 8192,
          .wr_buffers = wr_buffers,
          .uring_entries = 128,
          .sq_thread_cpu = sq_thread_cpu,
          .dbname_paths = dbname_paths}}
    , tdb{db} // open with latest finalized if valid, otherwise init as block 0
    , progress(
          monad_statesync_client_prefixes(),
          {db.get_latest_version(), db.get_latest_version()})
    , protocol(monad_statesync_client_prefixes())
    , tgrt{BlockHeader{.number = mpt::INVALID_BLOCK_NUM}}
    , current{db.get_latest_version() == mpt::INVALID_BLOCK_NUM ? 0 : db.get_latest_version() + 1}
    , n_upserts{0}
    , sync{sync}
    , statesync_send_request{statesync_send_request}
{
    MONAD_ASSERT(db.get_latest_version() == db.get_latest_finalized_version());
    // Statesync writes a single page-encoded timeline. A slot-encoded db, or a
    // db still carrying a secondary timeline from the dual-db migration, is
    // rejected rather than synced into.
    MONAD_ASSERT(tdb.is_page_encoded());
    MONAD_ASSERT(!db.timeline_active(timeline_id::secondary));
}

void monad_statesync_client_context::prepare_current_state()
{
    // Roll the db forward: upsert an empty finalized marker for the `current`
    // version and carry the state + code subtries over from `latest_version`.
    auto const latest_version = db.get_latest_version();
    UpdateList finalized_empty;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    finalized_empty.push_front(finalized);
    auto const src_root = db.load_root_for_version(latest_version);
    bool write_root = false;
    auto dest_root = db.upsert(
        src_root,
        std::move(finalized_empty),
        current,
        false,
        false,
        write_root);
    MONAD_ASSERT(db.find(dest_root, finalized_nibbles, current).has_value());

    auto const state_key = concat(FINALIZED_NIBBLE, STATE_NIBBLE);
    auto const code_key = concat(FINALIZED_NIBBLE, CODE_NIBBLE);
    dest_root = db.copy_trie(
        src_root,
        state_key,
        std::move(dest_root),
        state_key,
        current,
        write_root);
    write_root = true;
    dest_root = db.copy_trie(
        src_root,
        code_key,
        std::move(dest_root),
        code_key,
        current,
        write_root);
    auto const finalized_res = db.find(dest_root, finalized_nibbles, current);
    MONAD_ASSERT(finalized_res.has_value());
    MONAD_ASSERT(finalized_res.value().node->number_of_children() == 2);
    MONAD_ASSERT(db.find(dest_root, state_key, current).has_value());
    MONAD_ASSERT(db.find(dest_root, code_key, current).has_value());
    MONAD_ASSERT(dest_root->value() == src_root->value());
    tdb.reset_root(dest_root, current);
    MONAD_ASSERT(db.get_latest_version() == current);
}

void monad_statesync_client_context::commit()
{
    if (db.get_latest_version() != INVALID_BLOCK_NUM &&
        db.get_latest_version() != current) {
        prepare_current_state();
    }

    // UpdateList is intrusive: every Update node and the bytes it points at
    // must outlive the upsert below, so they are allocated in these deques.
    std::deque<mpt::Update> alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<monad_hash256> hash_alloc;

    // Build the page-encoded storage UpdateList for one account's deltas.
    // Slots are grouped by page_key and merged onto the page's current
    // contents, read from the trie on first touch, so several slot writes at
    // the same page_key compose into one update. A page that ends up empty
    // becomes a delete on the page entry. Pages from one account never
    // collide with another's, so no cross-account cache is needed.
    auto const build_page_storage = [&](Address const &addr,
                                        StorageDeltas const &slot_deltas) {
        UpdateList storage;
        ankerl::unordered_dense::segmented_map<
            bytes32_t,
            storage_page_t,
            BytesHashCompare<bytes32_t>>
            pages;
        for (auto const &[slot_key, slot_val] : slot_deltas) {
            auto const pg_key = compute_page_key(slot_key);
            auto const slot_off = compute_slot_offset(slot_key);
            auto [it, inserted] = pages.try_emplace(pg_key);
            if (inserted) {
                // Incarnation isn't tracked in statesync deltas; TrieDb
                // ignores it for storage reads, so a fixed value is fine.
                it->second =
                    tdb.read_storage_page(addr, Incarnation{0, 0}, pg_key);
            }
            it->second.set(slot_off, slot_val);
        }
        for (auto const &[page_key, page] : pages) {
            bool const is_empty = page.is_empty();
            storage.push_front(alloc.emplace_back(Update{
                .key = hash_alloc.emplace_back(
                    keccak256({page_key.bytes, sizeof(page_key.bytes)})),
                .value = is_empty
                             ? std::nullopt
                             : std::make_optional<byte_string_view>(
                                   bytes_alloc.emplace_back(
                                       encode_storage_page_db(page_key, page))),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(current)}));
        }
        return storage;
    };

    UpdateList accounts;
    for (auto const &[addr, delta] : deltas) {
        UpdateList storage;
        std::optional<byte_string_view> value;
        if (delta.has_value()) {
            auto const &[acct, slot_deltas] = delta.value();
            value = bytes_alloc.emplace_back(encode_account_db(addr, acct));
            storage = build_page_storage(addr, slot_deltas);
        }
        accounts.push_front(alloc.emplace_back(Update{
            .key = hash_alloc.emplace_back(keccak256(addr.bytes)),
            .value = value,
            .incarnation = false,
            .next = std::move(storage),
            .version = static_cast<int64_t>(current)}));
    }
    UpdateList code_updates;
    for (auto const &[hash, bytes] : code) {
        code_updates.push_front(alloc.emplace_back(Update{
            .key = NibblesView{hash},
            .value = bytes,
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(current)}));
    }

    auto const header_rlp = rlp::encode_block_header(tgrt);
    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(accounts),
        .version = static_cast<int64_t>(current)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(current)};
    auto block_header_update = Update{
        .key = block_header_nibbles,
        .value = header_rlp,
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(block_header_update);

    UpdateList finalized_updates;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(current)};
    finalized_updates.push_front(finalized);

    tdb.reset_root(
        db.upsert(
            tdb.get_root(),
            std::move(finalized_updates),
            current,
            false,
            false),
        current);

    code.clear();
    deltas.clear();
}
