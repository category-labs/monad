#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/execution/block_hash_buffer.hpp>

#include <quill/Quill.h>

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
    bytes32_t const &h, uint64_t const round, uint64_t const parent_round,
    BlockHashBufferFinalized const &buf)
    : n_{buf.n() + 1}
    , round_{round}
    , parent_round_{parent_round}
    , buf_{&buf}
    , deltas_{h}
{
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &h, uint64_t const round, uint64_t const parent_round,
    BlockHashBufferProposal const &parent)
    : n_{parent.n_ + 1}
    , round_{round}
    , parent_round_{parent_round}
    , buf_{parent.buf_}
{
    MONAD_ASSERT(parent_round < round);
    MONAD_ASSERT(n_ > 0 && n_ > buf_->n());
    deltas_.push_back(h);
    deltas_.insert(deltas_.end(), parent.deltas_.begin(), parent.deltas_.end());
    deltas_.resize(n_ - buf_->n());
}

uint64_t BlockHashBufferProposal::n() const
{
    return n_;
}

uint64_t BlockHashBufferProposal::round() const
{
    return round_;
}

uint64_t BlockHashBufferProposal::parent_round() const
{
    return parent_round_;
}

bytes32_t const &BlockHashBufferProposal::h() const
{
    return deltas_.front();
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
    , finalized_{buf.n() - 1}
{
}

BlockHashBuffer const &BlockHashChain::propose(
    bytes32_t const &hash, uint64_t const round, uint64_t const parent_round)
{
    for (auto it = proposals_.rbegin(); it != proposals_.rend();) {
        if (it->round() == round) {
            // delete duplicate
            it = std::reverse_iterator(proposals_.erase(std::next(it).base()));
            continue;
        }
        else if (it->round() == parent_round) {
            return proposals_.emplace_back(hash, round, parent_round, *it);
        }
        ++it;
    }
    return proposals_.emplace_back(hash, round, parent_round, buf_);
}

BlockHashBuffer const &BlockHashChain::finalize(uint64_t const round)
{
    auto const to_finalize = finalized_ + 1;
    auto winner_it = proposals_.begin();

    for (; winner_it != proposals_.end() && winner_it->round() != round;
         ++winner_it) {
    }
    if (MONAD_UNLIKELY(winner_it == proposals_.end())) {
        return buf_;
    }
    MONAD_ASSERT(winner_it->round() == round);
    MONAD_ASSERT((winner_it->n() - 1) == to_finalize);

    buf_.set(to_finalize, winner_it->h());
    finalized_ = to_finalize;

    // cleanup chains
    for (auto it = proposals_.begin(); it != proposals_.end();) {
        if (it->round() <= round) {
            it = proposals_.erase(it);
        }
        else {
            ++it;
        }
    }

    return buf_;
}

BlockHashBuffer const &
BlockHashChain::find_chain(uint64_t const parent_round) const
{
    for (auto it = proposals_.rbegin(); it != proposals_.rend(); ++it) {
        if (it->round() == parent_round) {
            return *it;
        }
    }
    return buf_;
}

bool init_block_hash_buffer(
    mpt::Db &rodb, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    TrieDb tdb{rodb};
    for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
         b < block_number;
         ++b) {
        tdb.set_block_number(b);
        auto const header = tdb.read_header();
        if (MONAD_UNLIKELY(!header.has_value())) {
            // changed to warning, bc it's not fatal for eth_call
            LOG_WARNING("Could not query block header {} from TrieDb", b);
            return false;
        }
        auto const h = std::bit_cast<bytes32_t>(
            keccak256(rlp::encode_block_header(header.value())));
        block_hash_buffer.set(b, h);
    }
    return true;
}

bool init_block_hash_buffer(
    BlockDb &block_db, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 1 : block_number - 255;
         b <= block_number;
         ++b) {
        Block block;
        auto const ok = block_db.get(b, block);
        if (MONAD_UNLIKELY(!ok)) {
            // same as above
            LOG_WARNING("Could not query block {} from blockdb.", b);
            return false;
        }
        block_hash_buffer.set(b - 1, block.header.parent_hash);
    }
    return true;
}

MONAD_NAMESPACE_END
