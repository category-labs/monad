// Copyright (C) 2026 Category Labs, Inc.
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
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/partitioned_commit_builder.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;
using namespace monad::partitioned;

PartitionedCommitBuilder::PartitionedCommitBuilder(
    uint64_t const block_number, ::monad::Db &db)
    : CommitBuilder{block_number}
    , db_{db}
{
}

Update &
PartitionedCommitBuilder::leaf_update(Nibbles key, bytes32_t const &value)
{
    auto const &v = value_alloc_.emplace_back(value);
    return update_alloc_.emplace_back(Update{
        .key = NibblesView{nibbles_alloc_.emplace_back(std::move(key))},
        .value = to_byte_string_view(v.bytes),
        .incarnation = false,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)});
}

Update &PartitionedCommitBuilder::erase_update(Nibbles key)
{
    return update_alloc_.emplace_back(Update{
        .key = NibblesView{nibbles_alloc_.emplace_back(std::move(key))},
        .value = std::nullopt,
        .incarnation = false,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)});
}

CommitBuilder &
PartitionedCommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    UpdateList state_updates;
    for (auto const &[addr, delta] : state_deltas) {
        auto const &before = delta.account.first;
        auto const &account = delta.account.second;
        proposal_post_state_.accounts[addr] = account;

        bool const existed = before.has_value();
        if (!account.has_value()) {
            if (!existed) {
                continue;
            }
            // Deletion drops the header stem and, if the account ever wrote
            // a slot outside the header, its storage stem.
            state_updates.push_front(erase_update(header_stem_nibbles(addr)));
            if (db_.storage_bucket_exists(addr)) {
                state_updates.push_front(
                    erase_update(storage_stem_nibbles(addr)));
            }
            continue;
        }

        bool const recreated =
            existed && before->incarnation != account->incarnation;
        bool const fresh = !existed || recreated;

        UpdateList storage_updates;

        // Storage: header slots merge into the account leaf's page, zone
        // slots are leaves under the storage stem
        auto const inc = account->incarnation;
        std::optional<storage_page_t> header_page;
        auto const header = [&]() -> storage_page_t & {
            if (!header_page.has_value()) {
                header_page =
                    fresh ? storage_page_t{}
                          : db_.read_storage_page(addr, inc, HEADER_PAGE_KEY);
            }
            return *header_page;
        };
        for (auto const &[key, storage_delta] : delta.storage) {
            if (storage_delta.first == storage_delta.second) {
                continue;
            }
            if (is_header_slot(key)) {
                header().set(header_slot_offset(key), storage_delta.second);
                continue;
            }
            auto const loc = locate_storage(addr, key);
            MONAD_ASSERT(!loc.in_header);
            Nibbles leaf_key = concat(
                NibblesView{hash_nibbles(loc.group_position)},
                NibblesView{sub_index_nibbles(loc.sub_index)});
            if (storage_delta.second == bytes32_t{}) {
                storage_updates.push_front(erase_update(std::move(leaf_key)));
            }
            else {
                storage_updates.push_front(
                    leaf_update(std::move(leaf_key), storage_delta.second));
            }
            proposal_post_state_.storage[::monad::StorageKey{addr, inc, key}] =
                storage_page_t{storage_delta.second};
        }

        // The account leaf at the header stem key: rewritten on any change
        // of its fields or header slots, carrying the whole header page
        if (fresh || *before != *account || header_page.has_value()) {
            state_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{nibbles_alloc_.emplace_back(
                    header_stem_nibbles(addr))},
                .value = bytes_alloc_.emplace_back(
                    encode_account_leaf(*account, header())),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_number_)}));
            proposal_post_state_
                .storage[::monad::StorageKey{addr, inc, HEADER_PAGE_KEY}] =
                header();
        }
        if (!storage_updates.empty()) {
            state_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{nibbles_alloc_.emplace_back(
                    storage_stem_nibbles(addr))},
                .value = byte_string_view{},
                .incarnation = recreated,
                .next = std::move(storage_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
        else if (recreated && db_.storage_bucket_exists(addr)) {
            state_updates.push_front(erase_update(storage_stem_nibbles(addr)));
        }
    }

    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(state_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

MONAD_NAMESPACE_END
