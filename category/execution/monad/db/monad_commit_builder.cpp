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

#include <category/execution/monad/db/monad_commit_builder.hpp>

#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/page_storage_cache.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

MonadCommitBuilder::MonadCommitBuilder(
    uint64_t const block_number, PageStorageCache &cache,
    monad_revision const rev)
    : CommitBuilder{block_number}
    , cache_{cache}
    , revision_{rev}
{
}

CommitBuilder &
MonadCommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    if (revision_ < MONAD_NEXT) {
        return CommitBuilder::add_state_deltas(state_deltas);
    }

    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        if (account.has_value()) {
            Incarnation const inc = account->incarnation;

            struct PageEntry
            {
                bytes32_t key;
                storage_page_t page;
            };

            std::vector<PageEntry> pages;

            for (auto const &[key, slot_delta] : delta.storage) {
                if (slot_delta.first != slot_delta.second) {
                    auto const pg_key = compute_page_key(key);
                    auto const slot_off = compute_slot_offset(key);

                    auto it = std::find_if(
                        pages.begin(), pages.end(), [&](PageEntry const &e) {
                            return e.key == pg_key;
                        });
                    if (it == pages.end()) {
                        pages.push_back(
                            {pg_key,
                             cache_.read_storage_page(addr, inc, pg_key)});
                        it = std::prev(pages.end());
                    }
                    it->page[slot_off] = slot_delta.second;
                }
            }

            for (auto const &[page_key, page] : pages) {
                storage_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = hash_alloc_.emplace_back(
                        keccak256({page_key.bytes, sizeof(page_key.bytes)})),
                    .value =
                        page.is_empty()
                            ? std::nullopt
                            : std::make_optional<byte_string_view>(
                                  bytes_alloc_.emplace_back(encode_storage_db(
                                      page_key,
                                      rle_encode(
                                          page.slots[0].bytes,
                                          sizeof(storage_page_t))))),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(block_number_)}));
            }
            value = bytes_alloc_.emplace_back(
                encode_account_db(addr, account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = hash_alloc_.emplace_back(
                    keccak256({addr.bytes, sizeof(addr.bytes)})),
                .value = value,
                .incarnation = incarnation,
                .next = std::move(storage_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
    }

    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

MONAD_NAMESPACE_END
