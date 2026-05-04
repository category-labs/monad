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

#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/page_storage_broker.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/update.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <algorithm>

#include <deque>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::optional<unsigned> const sq_thread_cpu, unsigned const wr_buffers,
    monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request),
    std::optional<std::filesystem::path> const secondary_db_path)
    : db{std::make_unique<OnDiskMachine>(),
         mpt::OnDiskDbConfig{
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

    if (secondary_db_path.has_value()) {
        secondary_db.emplace(
            std::make_unique<MonadOnDiskMachine>(),
            mpt::OnDiskDbConfig{
                .append = true,
                .compaction = false,
                .rewind_to_latest_finalized = true,
                .rd_buffers = 8192,
                .wr_buffers = wr_buffers,
                .uring_entries = 128,
                .sq_thread_cpu = sq_thread_cpu,
                .dbname_paths = {*secondary_db_path}});
        secondary_tdb.emplace(*secondary_db);
        // Secondary must be in lockstep with primary on latest finalized
        // version; statesync assumes both databases advance together.
        MONAD_ASSERT(
            secondary_db->get_latest_version() ==
            secondary_db->get_latest_finalized_version());
        MONAD_ASSERT(
            secondary_db->get_latest_version() == db.get_latest_version());
    }
}

void monad_statesync_client_context::prepare_current_state()
{
    // Roll forward `target_db`: upsert an empty finalized marker for the
    // `current` version and carry the state + code subtries over from
    // `latest_version`.
    auto const roll_forward = [&](mpt::Db &target_db, TrieDb &target_tdb) {
        auto const latest_version = target_db.get_latest_version();
        UpdateList finalized_empty;
        Update finalized{
            .key = finalized_nibbles,
            .value = byte_string_view{},
            .incarnation = true,
            .next = UpdateList{},
            .version = static_cast<int64_t>(current)};
        finalized_empty.push_front(finalized);
        auto const src_root = target_db.load_root_for_version(latest_version);
        bool write_root = false;
        auto dest_root = target_db.upsert(
            src_root,
            std::move(finalized_empty),
            current,
            false,
            false,
            write_root);
        MONAD_ASSERT(
            target_db.find(dest_root, finalized_nibbles, current).has_value());

        auto const state_key = concat(FINALIZED_NIBBLE, STATE_NIBBLE);
        auto const code_key = concat(FINALIZED_NIBBLE, CODE_NIBBLE);
        dest_root = target_db.copy_trie(
            src_root,
            state_key,
            std::move(dest_root),
            state_key,
            current,
            write_root);
        write_root = true;
        dest_root = target_db.copy_trie(
            src_root,
            code_key,
            std::move(dest_root),
            code_key,
            current,
            write_root);
        auto const finalized_res =
            target_db.find(dest_root, finalized_nibbles, current);
        MONAD_ASSERT(finalized_res.has_value());
        MONAD_ASSERT(finalized_res.value().node->number_of_children() == 2);
        MONAD_ASSERT(target_db.find(dest_root, state_key, current).has_value());
        MONAD_ASSERT(target_db.find(dest_root, code_key, current).has_value());
        MONAD_ASSERT(dest_root->value() == src_root->value());
        target_tdb.reset_root(dest_root, current);
        MONAD_ASSERT(target_db.get_latest_version() == current);
    };

    roll_forward(db, tdb);
    if (secondary_db.has_value()) {
        roll_forward(*secondary_db, *secondary_tdb);
    }
}

void monad_statesync_client_context::commit()
{
    if (db.get_latest_version() != INVALID_BLOCK_NUM &&
        db.get_latest_version() != current) {
        prepare_current_state();
    }

    // Build the encoded block header once; it's identical for both dbs.
    auto const header_rlp = rlp::encode_block_header(tgrt);

    // Build a slot-encoded storage UpdateList for an account's deltas.
    auto build_slot_storage = [this](
                                  StorageDeltas const &slot_deltas,
                                  std::deque<mpt::Update> &alloc,
                                  std::deque<byte_string> &bytes_alloc,
                                  std::deque<hash256> &hash_alloc) {
        UpdateList storage;
        for (auto const &[key, val] : slot_deltas) {
            storage.push_front(alloc.emplace_back(Update{
                .key = hash_alloc.emplace_back(keccak256(key.bytes)),
                .value = val == bytes32_t{}
                             ? std::nullopt
                             : std::make_optional<byte_string_view>(
                                   bytes_alloc.emplace_back(
                                       encode_storage_db(key, val))),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(current)}));
        }
        return storage;
    };

    // Build a page-encoded storage UpdateList for Db2. Slots are grouped by
    // page_key; existing pages are read through the broker so new slots are
    // merged onto any prior contents. A page that ends up empty becomes a
    // delete on the page entry.
    auto build_page_storage = [this](
                                  Address const &addr,
                                  StorageDeltas const &slot_deltas,
                                  PageStorageBroker &broker,
                                  std::deque<mpt::Update> &alloc,
                                  std::deque<byte_string> &bytes_alloc,
                                  std::deque<hash256> &hash_alloc) {
        UpdateList storage;
        struct PageEntry
        {
            bytes32_t key;
            storage_page_t page;
        };
        std::vector<PageEntry> pages;
        for (auto const &[slot_key, slot_val] : slot_deltas) {
            auto const pg_key = compute_page_key(slot_key);
            auto const slot_off = compute_slot_offset(slot_key);
            auto it = std::find_if(
                pages.begin(), pages.end(), [&](PageEntry const &e) {
                    return e.key == pg_key;
                });
            if (it == pages.end()) {
                // Incarnation isn't tracked in statesync deltas; TrieDb
                // ignores it for storage reads, so a fixed value is fine.
                pages.push_back(
                    {pg_key,
                     broker.read_storage_page(
                         addr, Incarnation{0, 0}, pg_key)});
                it = std::prev(pages.end());
            }
            it->page[slot_off] = slot_val;
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

    // Assemble the full finalized/state/code/block_header UpdateList for one
    // db and upsert it. Storage encoding is delegated via `build_storage`,
    // and `state_marker` is stamped as the value of the top-level
    // state_nibbles entry (empty for slot, page_encoding_marker for page).
    auto build_and_upsert = [this, &header_rlp](
                                mpt::Db &target_db,
                                TrieDb &target_tdb,
                                byte_string_view const state_marker,
                                auto build_storage) {
        std::deque<mpt::Update> alloc;
        std::deque<byte_string> bytes_alloc;
        std::deque<hash256> hash_alloc;

        UpdateList accounts;
        for (auto const &[addr, delta] : deltas) {
            UpdateList storage;
            std::optional<byte_string_view> value;
            if (delta.has_value()) {
                auto const &[acct, slot_deltas] = delta.value();
                value = bytes_alloc.emplace_back(encode_account_db(addr, acct));
                storage = build_storage(
                    addr, slot_deltas, alloc, bytes_alloc, hash_alloc);
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

        auto state_update = Update{
            .key = state_nibbles,
            .value = state_marker,
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

        target_tdb.reset_root(
            target_db.upsert(
                target_tdb.get_root(),
                std::move(finalized_updates),
                current,
                false,
                false),
            current);
    };

    // Primary: slot-encoded storage.
    build_and_upsert(
        db,
        tdb,
        byte_string_view{},
        [&](Address const &,
            StorageDeltas const &slot_deltas,
            std::deque<mpt::Update> &alloc,
            std::deque<byte_string> &bytes_alloc,
            std::deque<hash256> &hash_alloc) {
            return build_slot_storage(
                slot_deltas, alloc, bytes_alloc, hash_alloc);
        });

    // Secondary: page-encoded storage. The broker's lifetime covers the
    // full loop so the per-account merges see each other's writes through
    // the same cache.
    if (secondary_db.has_value()) {
        PageStorageBroker broker{*secondary_tdb};
        build_and_upsert(
            *secondary_db,
            *secondary_tdb,
            byte_string_view{page_encoding_marker},
            [&](Address const &addr,
                StorageDeltas const &slot_deltas,
                std::deque<mpt::Update> &alloc,
                std::deque<byte_string> &bytes_alloc,
                std::deque<hash256> &hash_alloc) {
                return build_page_storage(
                    addr, slot_deltas, broker, alloc, bytes_alloc, hash_alloc);
            });
    }

    code.clear();
    deltas.clear();
}
