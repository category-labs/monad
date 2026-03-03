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

#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/page_storage_cache.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/monad_commit_builder.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::optional<unsigned> const sq_thread_cpu,
    monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
    : db{machine,
         mpt::OnDiskDbConfig{
             .append = true,
             .compaction = false,
             .rewind_to_latest_finalized = true,
             .rd_buffers = 8192,
             .wr_buffers = 32,
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
}

void monad_statesync_client_context::prepare_current_state()
{
    auto const latest_version = db.get_latest_version();
    // commit empty finalized state to current first
    UpdateList finalized_empty;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    finalized_empty.push_front(finalized);
    bool write_root = false;
    auto dest_root = db.upsert(
        nullptr, std::move(finalized_empty), current, false, false, write_root);
    MONAD_ASSERT(db.find(dest_root, finalized_nibbles, current).has_value());

    // move state and code from latest finalized to current
    auto const src_root = db.load_root_for_version(latest_version);
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
    tdb.reset_root(dest_root, current);
    MONAD_ASSERT(db.get_latest_version() == current);
}

void monad_statesync_client_context::commit()
{
    if (db.get_latest_version() != INVALID_BLOCK_NUM &&
        db.get_latest_version() != current) {
        prepare_current_state();
    }

    monad::StateDeltas state_deltas;
    for (auto const &[addr, delta] : deltas) {
        if (delta.has_value()) {
            auto const &[acct, storage] = delta.value();
            monad::StateDelta sd{
                .account = AccountDelta{std::nullopt, acct}, .storage = {}};
            for (auto const &[key, val] : storage) {
                if (val != bytes32_t{}) {
                    sd.storage.emplace(
                        key, monad::StorageDelta{bytes32_t{}, val});
                }
                else {
                    sd.storage.emplace(
                        key, monad::StorageDelta{bytes32_t{1}, bytes32_t{}});
                }
            }
            state_deltas.emplace(addr, std::move(sd));
        }
        else {
            state_deltas.emplace(
                addr,
                monad::StateDelta{
                    .account = AccountDelta{Account{}, std::nullopt},
                    .storage = {}});
        }
    }

    NoopStorageCache cache{tdb};
    MonadCommitBuilder builder{current, cache, machine.revision};
    builder.add_state_deltas(state_deltas);
    builder.add_raw_code(code);

    auto finalized_updates = builder.build(finalized_nibbles);
    auto const header_rlp = rlp::encode_block_header(tgrt);
    Update block_header_update{
        .key = block_header_nibbles,
        .value = header_rlp,
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    finalized_updates.front().next.push_front(block_header_update);

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
