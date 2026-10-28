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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/update.hpp>

#include <deque>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct CallFrame;
struct Transaction;
struct BlockHeader;
struct Receipt;
struct Withdrawal;

// One derived private domain block, as committed with the L1 block it was
// derived from. See docs/domains-protocol.md.
struct DomainBlockCommit
{
    uint64_t domain_chain_id;
    uint64_t number;
    // rlp(ProposedDomainHeader)
    byte_string_view encoded_header;
    std::span<Transaction const> transactions;
    std::span<Address const> senders;
};

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

public:
    explicit CommitBuilder(uint64_t block_number);
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

    // The private domain blocks derived from this block, at most one per
    // domain. Called with every block, with or without domain blocks, by
    // nodes that derive private domains, and by no others.
    CommitBuilder &add_domain_blocks(std::span<DomainBlockCommit const>);

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
