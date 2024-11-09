#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_buffer.hpp>

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

BlockHashChain::BlockHashChain(
    BlockHashBufferFinalized &buf, uint64_t last_finalized_round)
    : buf_{buf}
    , last_finalized_round_{last_finalized_round}
{
}

void BlockHashChain::propose(
    bytes32_t const &hash, uint64_t const round, uint64_t const parent_round)
{
    for (auto it = proposals_.rbegin(); it != proposals_.rend(); ++it) {
        if (it->round == parent_round) {
            proposals_.emplace_back(Proposal{
                .round = round,
                .parent_round = parent_round,
                .buf = BlockHashBufferProposal(hash, it->buf)});
            return;
        }
    }
    MONAD_ASSERT(parent_round == last_finalized_round_);
    proposals_.emplace_back(Proposal{
        .round = round,
        .parent_round = parent_round,
        .buf = BlockHashBufferProposal(hash, buf_)});
}

void BlockHashChain::finalize(uint64_t const round)
{
    auto const to_finalize = buf_.n();

    auto winner_it = std::find_if(
        proposals_.rbegin(), proposals_.rend(), [round](Proposal const &p) {
            return round == p.round;
        });
    MONAD_ASSERT(winner_it != proposals_.rend())
    MONAD_ASSERT((winner_it->buf.n() - 1) == to_finalize);

    buf_.set(to_finalize, winner_it->buf.get(to_finalize));
    last_finalized_round_ = round;

    // cleanup chains
    std::remove_if(
        proposals_.begin(), proposals_.end(), [round](Proposal const &p) {
            return round <= p.round;
        });
}

BlockHashBuffer const &BlockHashChain::find_chain(uint64_t const round) const
{
    auto it = std::find_if(
        proposals_.rbegin(), proposals_.rend(), [round](Proposal const &p) {
            return round == p.round;
        });
    if (MONAD_UNLIKELY(it == proposals_.rend())) {
        MONAD_ASSERT(round == last_finalized_round_)
        return buf_;
    }
    return it->buf;
}

MONAD_NAMESPACE_END
