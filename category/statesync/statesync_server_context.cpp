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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/util.hpp>
#include <category/statesync/statesync_server_context.hpp>
#include <category/vm/code.hpp>

#include <algorithm>
#include <cstdint>
#include <deque>
#include <functional>
#include <memory>
#include <mutex>
#include <optional>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas,
    uint64_t const n, bytes32_t const &block_id)
{
    auto &proposals = ctx.proposals;

    auto &deletions =
        proposals
            .emplace_back(ProposedDeletions{
                .block_number = n, .block_id = block_id, .deletions = {}})
            .deletions;

    for (auto const &[addr, delta] : state_deltas) {
        auto const &account = delta.account.second;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second &&
                    delta.second == bytes32_t{}) {
                    LOG_DEBUG(
                        "Deleting Storage n={} addr={} storage={} ",
                        n,
                        addr,
                        key);
                    deletions.emplace_back(addr, key);
                }
            }
        }

        if (delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            if (incarnation || !account.has_value()) {
                deletions.emplace_back(addr, std::nullopt);
            }
        }
    }
}

void on_finalize(
    monad_statesync_server_context &ctx, uint64_t const block_number,
    bytes32_t const &block_id)
{
    auto &proposals = ctx.proposals;

    auto const it = std::find_if(
        proposals.begin(), proposals.end(), [&block_id](auto const &p) {
            return p.block_id == block_id;
        });

    if (MONAD_UNLIKELY(it == proposals.end())) {
        return;
    }

    MONAD_ASSERT(it->block_number == block_number);

    ctx.deletions.write(block_number, std::move(it->deletions));

    // gc proposals of older blocks than finalized block
    std::erase_if(proposals, [block_number](ProposedDeletions const &p) {
        return p.block_number <= block_number;
    });
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

FinalizedDeletions::Entry FinalizedDeletions::find(uint64_t const block_number)
{
    std::lock_guard const lock{mutex_};
    if (block_number < start_block_number_ ||
        block_number - start_block_number_ >= entries_.size()) {
        return nullptr;
    }
    return entries_[block_number - start_block_number_];
}

void FinalizedDeletions::write(
    uint64_t const block_number, std::vector<Deletion> deletions)
{
    MONAD_ASSERT(block_number != INVALID_BLOCK_NUM);
    auto entry =
        std::make_shared<std::vector<Deletion> const>(std::move(deletions));

    std::lock_guard const lock{mutex_};
    if (MONAD_UNLIKELY(start_block_number_ == INVALID_BLOCK_NUM)) {
        start_block_number_ = block_number;
    }
    MONAD_ASSERT(start_block_number_ + entries_.size() == block_number);

    if (MONAD_UNLIKELY(entry->size() > MAX_DELETIONS)) {
        LOG_WARNING(
            "dropping deletions due to excessive size block_number={} size={}",
            block_number,
            entry->size());
        entries_.clear();
        num_deletions_ = 0;
        start_block_number_ = block_number + 1;
        return;
    }
    while (entries_.size() == MAX_ENTRIES ||
           num_deletions_ + entry->size() > MAX_DELETIONS) {
        num_deletions_ -= entries_.front()->size();
        entries_.pop_front();
        ++start_block_number_;
    }
    num_deletions_ += entry->size();
    entries_.push_back(std::move(entry));
    LOG_DEBUG(
        "deletions buffer range=[{}, {}] num_deletions={}",
        start_block_number_,
        block_number,
        num_deletions_);
}

MONAD_NAMESPACE_END

monad_statesync_server_context::monad_statesync_server_context(TrieDb &rw)
    : rw{rw}
    , ro{nullptr}
{
    // The server traversal expands page leaves into slot-format upserts and
    // has no slot-encoded path.
    MONAD_ASSERT(rw.is_page_encoded());
}

bool monad_statesync_server_context::is_page_encoded() const
{
    return rw.is_page_encoded();
}

std::optional<Account>
monad_statesync_server_context::read_account(Address const &addr)
{
    return rw.read_account(addr);
}

bytes32_t monad_statesync_server_context::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    return rw.read_storage(addr, incarnation, key);
}

storage_page_t monad_statesync_server_context::read_storage_page(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &page_key)
{
    return rw.read_storage_page(addr, incarnation, page_key);
}

monad::vm::SharedIntercode
monad_statesync_server_context::read_code(bytes32_t const &hash)
{
    return rw.read_code(hash);
}

monad::BlockHeader monad_statesync_server_context::read_eth_header()
{
    return rw.read_eth_header();
}

bytes32_t monad_statesync_server_context::state_root()
{
    return rw.state_root();
}

bytes32_t monad_statesync_server_context::receipts_root()
{
    return rw.receipts_root();
}

bytes32_t monad_statesync_server_context::transactions_root()
{
    return rw.transactions_root();
}

std::optional<bytes32_t> monad_statesync_server_context::withdrawals_root()
{
    return rw.withdrawals_root();
}

void monad_statesync_server_context::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
    rw.set_block_and_prefix(block_number, block_id);
}

void monad_statesync_server_context::finalize(
    uint64_t const block_number, bytes32_t const &block_id)
{
    on_finalize(*this, block_number, block_id);
    rw.finalize(block_number, block_id);
}

void monad_statesync_server_context::update_verified_block(
    uint64_t const block_number)
{
    rw.update_verified_block(block_number);
}

void monad_statesync_server_context::update_voted_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    rw.update_voted_metadata(block_number, block_id);
}

void monad_statesync_server_context::update_proposed_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    rw.update_proposed_metadata(block_number, block_id);
}

void monad_statesync_server_context::commit(
    bytes32_t const &block_id, CommitBuilder &builder,
    BlockHeader const &header, StateDeltas const &state_deltas,
    std::function<void(BlockHeader &)> populate_header_fn)
{
    on_commit(*this, state_deltas, header.number, block_id);
    rw.commit(
        block_id, builder, header, state_deltas, std::move(populate_header_fn));
}

uint64_t monad_statesync_server_context::get_block_number() const
{
    return rw.get_block_number();
}
