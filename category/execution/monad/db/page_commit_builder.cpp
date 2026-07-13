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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/account_key.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/update.hpp>

#include <ankerl/unordered_dense.h>
#include <intx/intx.hpp>

#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    void build_page_account_updates(
        monad::Db &db, StateDeltas const &state_deltas,
        ProposalPostState &post_state, std::optional<uint64_t> const ns,
        UpdateList &account_updates, std::deque<Update> &update_alloc,
        std::deque<byte_string> &bytes_alloc, std::deque<hash256> &hash_alloc,
        uint64_t const block_number)
    {
        for (auto const &[addr, delta] : state_deltas) {
            UpdateList storage_updates;
            std::optional<byte_string_view> value;
            auto const &account = delta.account.second;
            post_state.accounts[AccountKey{addr, ns}] = account;
            bool const reincarnated =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            if (account.has_value()) {
                Incarnation const inc = account->incarnation;
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
                            it->second = reincarnated
                                             ? storage_page_t{}
                                             : db.read_storage_page(
                                                   addr, inc, pg_key, ns);
                        }
                        it->second.set(slot_off, slot_delta.second);
                    }
                }

                for (auto const &[page_key, page] : pages) {
                    bool const is_empty = page.is_empty();
                    post_state.storage[StorageKey{addr, inc, page_key, ns}] =
                        page;
                    storage_updates.push_front(update_alloc.emplace_back(Update{
                        .key = hash_alloc.emplace_back(keccak256(
                            {page_key.bytes, sizeof(page_key.bytes)})),
                        .value = is_empty
                                     ? std::nullopt
                                     : std::make_optional<byte_string_view>(
                                           bytes_alloc.emplace_back(
                                               encode_storage_page_db(
                                                   page_key, page))),
                        .incarnation = false,
                        .next = UpdateList{},
                        .version = static_cast<int64_t>(block_number)}));
                }
                value =
                    bytes_alloc.emplace_back(encode_account_db(addr, *account));
            }

            if (!storage_updates.empty() || delta.account.first != account) {
                account_updates.push_front(update_alloc.emplace_back(Update{
                    .key = hash_alloc.emplace_back(
                        keccak256({addr.bytes, sizeof(addr.bytes)})),
                    .value = value,
                    .incarnation = reincarnated,
                    .next = std::move(storage_updates),
                    .version = static_cast<int64_t>(block_number)}));
            }
        }
    }
}

PageCommitBuilder::PageCommitBuilder(uint64_t const block_number, monad::Db &db)
    : CommitBuilder{block_number}
    , db_{db}
{
}

std::unique_ptr<CommitBuilder>
make_commit_builder(uint64_t const block_number, monad::Db &db)
{
    if (db.is_page_encoded()) {
        return std::make_unique<PageCommitBuilder>(block_number, db);
    }
    return std::make_unique<CommitBuilder>(block_number);
}

CommitBuilder &
PageCommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    UpdateList account_updates;
    build_page_account_updates(
        db_,
        state_deltas,
        proposal_post_state_,
        std::nullopt,
        account_updates,
        update_alloc_,
        bytes_alloc_,
        hash_alloc_,
        block_number_);

    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &PageCommitBuilder::add_namespace_state_deltas(
    NamespacedStateDeltas const &ns_deltas)
{
    UpdateList namespace_updates;
    for (auto const &[ns, inner] : ns_deltas) {
        MONAD_ASSERT(inner);
        UpdateList account_updates;
        build_page_account_updates(
            db_,
            *inner,
            namespace_proposal_post_state_[ns],
            std::optional<uint64_t>{ns},
            account_updates,
            update_alloc_,
            bytes_alloc_,
            hash_alloc_,
            block_number_);

        if (!account_updates.empty()) {
            uint8_t ns_bytes[sizeof(uint64_t)];
            intx::be::store(ns_bytes, ns);
            namespace_updates.push_front(update_alloc_.emplace_back(Update{
                .key = bytes_alloc_.emplace_back(ns_bytes, sizeof(ns_bytes)),
                .value = bytes_alloc_.emplace_back(rlp::encode_unsigned(ns)),
                .incarnation = false,
                .next = std::move(account_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
    }

    if (!namespace_updates.empty()) {
        updates_.push_front(update_alloc_.emplace_back(Update{
            .key = namespace_state_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(namespace_updates),
            .version = static_cast<int64_t>(block_number_)}));
    }

    return *this;
}

MONAD_NAMESPACE_END
