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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/mpt/update.hpp>

#include <deque>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Fixed-window cache inputs for one block's stamp selection: the journaled
// per-transaction read candidates (write candidates come from the deltas).
struct StampContext
{
    BlockStampCandidates const *candidates;
};

// Per-block stamp bookkeeping for the measurement log line.
struct StampBlockStats
{
    uint64_t accounts_written{0};
    uint64_t pages_written{0};
    uint64_t slots_written{0};
    uint64_t account_candidates[3]{0, 0, 0}; // class 1, 2, 3
    uint64_t page_candidates[3]{0, 0, 0};
    uint64_t selected_accounts{0};
    uint64_t selected_pages{0};
    uint64_t selected_slots{0};
    uint64_t dead_accounts{0};
    uint64_t dead_pages{0};
    bool account_cap_hit{false};
    bool page_cap_hit{false};
    uint64_t record_bytes{0};
    uint64_t log_pages{0};
    bytes32_t record_hash{};
    // the selected keys, in selection order (a copy for debugging dumps)
    std::vector<Address> selected_account_keys;
    std::vector<StorageKey> selected_storage_keys;
};

struct CallFrame;
struct Transaction;
struct BlockHeader;
struct Receipt;
struct Withdrawal;

class CommitBuilder
{
protected:
    std::deque<mpt::Update> update_alloc_;
    std::deque<byte_string> bytes_alloc_;
    std::deque<monad_hash256> hash_alloc_;
    mpt::UpdateList updates_;
    uint64_t block_number_;
    // Per-block post-state assembled by `add_state_deltas`.
    // Slot based storage fills it with single-slot storage page keyed by
    // storage slot key, Paged based storage fills it with the actual storage
    // page keyed by storage page key.
    ProposalPostState proposal_post_state_;
    StampContext const *stamps_{nullptr};
    StampBlockStats stamp_stats_{};
    // the state subtrie update pushed by add_state_deltas; the stamp log
    // account is appended to its nested account list
    mpt::Update *state_update_{nullptr};

    // Class the block's candidates (entry / write renewal / read refresh),
    // select by (class, weight, key) under the per-block caps, record the
    // selection in the proposal post-state, and write the stamp log record
    // as storage of STAMP_LOG_ADDRESS into the state update.
    void add_stamp_records(StateDeltas const &);

    void push_state_update(mpt::UpdateList &&account_updates);

    // Encoding hooks for stamp selection: the storage lookup key of a raw
    // slot key and the occupied-slot weight of a page that the block did not
    // write (slot encoding: the slot itself, weight 1).
    virtual bytes32_t stamp_lookup_key(bytes32_t const &key) const
    {
        return key;
    }

    virtual uint32_t
    stamp_read_weight(Address const &, Incarnation, bytes32_t const &) const
    {
        return 1;
    }

public:
    explicit CommitBuilder(
        uint64_t block_number, StampContext const *stamps = nullptr);
    virtual ~CommitBuilder() = default;

    virtual CommitBuilder &add_state_deltas(StateDeltas const &);

    CommitBuilder &add_code(Code const &);

    CommitBuilder &add_receipts(std::vector<Receipt> const &);

    CommitBuilder &add_transactions(
        std::vector<Transaction> const &, std::vector<Address> const &);

    CommitBuilder &add_call_frames(std::vector<std::vector<CallFrame>> const &);

    CommitBuilder &add_ommers(std::vector<BlockHeader> const &);

    CommitBuilder &add_withdrawals(std::vector<Withdrawal> const &);

    CommitBuilder &add_block_header(BlockHeader const &);

    // Consumes updates_ but preserves the backing deque storage. New updates
    // can be added after a build() call (e.g. add_block_header between the
    // two commit stages), but previously built updates are not retained.
    mpt::UpdateList build(mpt::NibblesView);

    // Move out the proposal post-state assembled by `add_state_deltas`.
    // Must be called after `add_state_deltas`; calling it twice yields an
    // empty struct the second time.
    ProposalPostState take_proposal_post_state()
    {
        return std::move(proposal_post_state_);
    }

    StampBlockStats const &stamp_stats() const
    {
        return stamp_stats_;
    }
};

MONAD_NAMESPACE_END
