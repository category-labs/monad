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
#include <category/mpt/update.hpp>

#include <deque>
#include <vector>

MONAD_NAMESPACE_BEGIN

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
    std::deque<hash256> hash_alloc_;
    mpt::UpdateList updates_;
    uint64_t block_number_;
    // Per-block post-state assembled by `add_state_deltas`.
    // Slot based storage fills it with single-slot storage page keyed by
    // storage slot key, Paged based storage fills it with the actual storage
    // page keyed by storage page key.
    ProposalPostState proposal_post_state_;

#if KVDB_PROTO
    // KV reuse: the already-encoded, DB-format values the KV blob writer stores
    // verbatim (byte-identical to triedb), so it never re-encodes on the commit
    // critical path. Views into bytes_alloc_/hash_alloc_ (a deque: refs stay
    // valid across push_back and across build(), which does not clear them).
    // Per-tx categories are indexed by tx position. Filled by the add_* below.
    std::vector<byte_string_view> kv_receipts_;
    std::vector<byte_string_view> kv_transactions_;
    std::vector<byte_string_view> kv_call_frames_; // full per-tx encoding (unchunked)
    std::vector<byte_string_view> kv_tx_hashes_; // keccak(encoded_tx), 32B each
    std::vector<byte_string_view> kv_withdrawals_;
    byte_string_view kv_ommers_;
#endif

public:
    explicit CommitBuilder(uint64_t block_number);
    virtual ~CommitBuilder() = default;

#if KVDB_PROTO
    std::vector<byte_string_view> const &kv_receipts() const
    {
        return kv_receipts_;
    }
    std::vector<byte_string_view> const &kv_transactions() const
    {
        return kv_transactions_;
    }
    std::vector<byte_string_view> const &kv_call_frames() const
    {
        return kv_call_frames_;
    }
    std::vector<byte_string_view> const &kv_tx_hashes() const
    {
        return kv_tx_hashes_;
    }
    std::vector<byte_string_view> const &kv_withdrawals() const
    {
        return kv_withdrawals_;
    }
    byte_string_view kv_ommers() const
    {
        return kv_ommers_;
    }
#endif

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
};

MONAD_NAMESPACE_END
