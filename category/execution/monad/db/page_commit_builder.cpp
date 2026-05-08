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

#include <category/core/bytes_hash_compare.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

PageCommitBuilder::PageCommitBuilder(uint64_t const block_number, monad::Db &db)
    : CommitBuilder{block_number}
    , db_{db}
{
}

CommitBuilder &
PageCommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        proposal_post_state_.accounts[addr] = account;
        if (account.has_value()) {
            Incarnation const inc = account->incarnation;

            // Page granularity per account: keyed by page_key, value is the
            // mutable storage_page_t being merged. Each first-touch of a
            // page reads the current page from the db so subsequent slot
            // writes at the same page_key compose into one update.
            ankerl::unordered_dense::segmented_map<
                bytes32_t,
                storage_page_t,
                BytesHashCompare<bytes32_t>>
                pages;

            for (auto const &[key, slot_delta] : delta.storage) {
                if (slot_delta.first != slot_delta.second) {
                    auto const pg_key = compute_page_key(key);
                    auto const slot_off = compute_slot_offset(key);
                    auto [it, inserted] = pages.try_emplace(pg_key);
                    if (inserted) {
                        it->second = db_.read_storage_page(addr, inc, pg_key);
                    }
                    it->second[slot_off] = slot_delta.second;
                }
            }

            for (auto const &[page_key, page] : pages) {
                bool const is_empty = page.is_empty();
                // Record the post-commit page bytes for the proposal cache.
                // For empty pages, store an empty byte_string so a later read
                // through the cache returns "no entry" — matching the trie,
                // which has no leaf at this path.
                StorageKey const sk{addr, inc, page_key};
                proposal_post_state_.storage[sk] =
                    is_empty ? byte_string{} : encode_storage_page(page);
                storage_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = hash_alloc_.emplace_back(
                        keccak256({page_key.bytes, sizeof(page_key.bytes)})),
                    .value = is_empty ? std::nullopt
                                      : std::make_optional<byte_string_view>(
                                            bytes_alloc_.emplace_back(
                                                encode_storage_page_db(
                                                    page_key, page))),
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
