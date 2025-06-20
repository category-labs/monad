#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/execution/fee_buffer.hpp>

MONAD_NAMESPACE_BEGIN

void FeeBuffer::set(
    uint64_t const block_number, uint64_t const round,
    uint64_t const parent_round)
{
    MONAD_ASSERT(fees_.empty());
    block_number_ = block_number;
    round_ = round;
    parent_round_ = parent_round;
}

void FeeBuffer::note(unsigned const i, Address const &a, uint512_t const fee)
{
    MONAD_ASSERT(fees_[a].empty() || fees_[a].back().first < i);
    fees_[a].emplace_back(i, fee);
}

void FeeBuffer::propose()
{
    ProposalFees const &parent = proposals_.contains(parent_round_)
                                     ? proposals_.at(parent_round_)
                                     : ProposalFees{EXECUTION_DELAY};
    MONAD_ASSERT(
        proposals_
            .emplace(
                round_,
                parent.set(block_number_ % EXECUTION_DELAY, std::move(fees_)))
            .second);
    fees_.clear();
}

void FeeBuffer::finalize(uint64_t const round)
{
    std::erase_if(
        proposals_, [round](auto const &it) { return it.first < round; });
}

uint512_t FeeBuffer::sum(unsigned const i, Address const &a) const
{
    MONAD_ASSERT(proposals_.contains(round_));
    uint512_t sum = 0;
    bool found = false;
    auto const &proposals = proposals_.at(round_);
    for (unsigned j = 0; j < proposals.size(); ++j) {
        auto const &fees = proposals[j];
        if (!fees.contains(a)) {
            continue;
        }
        for (auto const &[k, fee] : fees.at(a)) {
            sum += fee;
            if ((j == block_number_ % EXECUTION_DELAY) && k == i) {
                found = true;
                break;
            }
        }
    }
    MONAD_ASSERT(found);
    return sum;
}

MONAD_NAMESPACE_END
