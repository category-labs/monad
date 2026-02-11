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
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/update.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <deque>
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
    std::deque<mpt::Update> alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<hash256> hash_alloc;
    UpdateList accounts;
    for (auto const &[addr, delta] : deltas) {
        UpdateList storage;
        std::optional<byte_string_view> value;
        if (delta.has_value()) {
            auto const &[acct, deltas] = delta.value();
            value = bytes_alloc.emplace_back(encode_account_db(addr, acct));
            for (auto const &[key, val] : deltas) {
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
    auto const rlp = rlp::encode_block_header(tgrt);
    auto block_header_update = Update{
        .key = block_header_nibbles,
        .value = rlp,
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
