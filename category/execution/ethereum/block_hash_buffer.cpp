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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

BlockHashBufferFinalized::BlockHashBufferFinalized()
    : b_{}
    , n_{0}
{
    for (auto &h : b_) {
        h = NULL_HASH;
    }
}

uint64_t BlockHashBufferFinalized::n() const
{
    return n_;
};

bytes32_t const &BlockHashBufferFinalized::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    return b_[n % N];
}

void BlockHashBufferFinalized::set(uint64_t const n, bytes32_t const &h)
{
    MONAD_ASSERT(!n_ || n == n_);
    b_[n % N] = h;
    n_ = n + 1;
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &h, BlockHashBufferFinalized const &buf)
    : n_{buf.n() + 1}
    , buf_{&buf}
    , deltas_{h}
{
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &h, BlockHashBufferProposal const &parent)
    : n_{parent.n_ + 1}
    , buf_{parent.buf_}
{
    MONAD_ASSERT(n_ > 0 && n_ > buf_->n());
    deltas_.push_back(h);
    deltas_.insert(deltas_.end(), parent.deltas_.begin(), parent.deltas_.end());
    deltas_.resize(n_ - buf_->n());
}

uint64_t BlockHashBufferProposal::n() const
{
    return n_;
}

bytes32_t const &BlockHashBufferProposal::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    size_t const idx = n_ - n - 1;
    if (idx < deltas_.size()) {
        return deltas_.at(idx);
    }
    return buf_->get(n);
}

BlockHashChain::BlockHashChain(BlockHashBufferFinalized &buf)
    : buf_{buf}
{
}

void BlockHashChain::propose(
    bytes32_t const &hash, uint64_t const block_number,
    bytes32_t const &block_id, bytes32_t const &parent_id)
{
    for (auto it = proposals_.begin(); it != proposals_.end(); ++it) {
        if (it->block_id == parent_id) {
            proposals_.emplace_back(Proposal{
                .block_number = block_number,
                .block_id = block_id,
                .parent_id = parent_id,
                .buf = BlockHashBufferProposal(hash, it->buf)});
            return;
        }
    }
    proposals_.emplace_back(Proposal{
        .block_number = block_number,
        .block_id = block_id,
        .parent_id = parent_id,
        .buf = BlockHashBufferProposal(hash, buf_)});
}

void BlockHashChain::finalize(bytes32_t const &block_id)
{
    auto const to_finalize = buf_.n();

    auto winner_it = std::find_if(
        proposals_.begin(), proposals_.end(), [&block_id](Proposal const &p) {
            return p.block_id == block_id;
        });
    MONAD_ASSERT(winner_it != proposals_.end());
    MONAD_ASSERT((winner_it->buf.n() - 1) == to_finalize);
    buf_.set(to_finalize, winner_it->buf.get(to_finalize));
    uint64_t const block_number = winner_it->block_number;

    // cleanup chains
    proposals_.erase(
        std::remove_if(
            proposals_.begin(),
            proposals_.end(),
            [block_number](Proposal const &p) {
                return p.block_number <= block_number;
            }),
        proposals_.end());
}

BlockHashBuffer const &
BlockHashChain::find_chain(bytes32_t const &block_id) const
{
    auto it = std::find_if(
        proposals_.begin(), proposals_.end(), [&block_id](Proposal const &p) {
            return p.block_id == block_id;
        });
    if (MONAD_UNLIKELY(it == proposals_.end())) {
        return buf_;
    }
    return it->buf;
}

bool init_block_hash_buffer_from_triedb(
    mpt::Db &rodb, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
         b < block_number;
         ++b) {
        auto const header = rodb.get(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            b);
        if (!header.has_value()) {
            LOG_WARNING(
                "Could not query block header {} from TrieDb -- {}",
                b,
                header.error().message().c_str());
            return false;
        }
        auto const h = to_bytes(keccak256(header.value()));
        block_hash_buffer.set(b, h);
    }

    return true;
}

bool init_block_hash_buffer_from_blockdb(
    BlockDb &block_db, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 1 : block_number - 255;
         b <= block_number;
         ++b) {
        Block block;
        auto const ok = block_db.get(b, block);
        if (!ok) {
            LOG_WARNING("Could not query block {} from blockdb.", b);
            return false;
        }
        block_hash_buffer.set(b - 1, block.header.parent_hash);
    }

    return true;
}

MONAD_NAMESPACE_END
