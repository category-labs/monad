#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/execution/block_reward.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <intx/intx.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>

MONAD_NAMESPACE_BEGIN

constexpr uint256_t calculate_block_reward(
    uint256_t const &reward, uint256_t const &ommer_reward,
    size_t const ommers_size)
{
    MONAD_DEBUG_ASSERT(
        intx::umul(ommer_reward, uint256_t{ommers_size}) <=
        std::numeric_limits<uint256_t>::max() - reward);

    return reward + ommer_reward * ommers_size;
}

constexpr uint256_t const calculate_ommer_reward(
    uint256_t const &reward, uint64_t const header_number,
    uint64_t const ommer_number)
{
    auto const subtrahend = ((header_number - ommer_number) * reward) / 8;
    return reward - subtrahend;
}

void apply_block_reward(
    BlockState &block_state, Block const &block, uint256_t const &block_reward,
    uint256_t const &ommer_reward)
{
    State state{block_state};
    auto const miner_reward =
        calculate_block_reward(block_reward, ommer_reward, block.ommers.size());

    // reward block beneficiary, YP Eqn. 172
    if (MONAD_LIKELY(miner_reward)) {
        state.add_to_balance(block.header.beneficiary, miner_reward);
    }

    // reward ommers, YP Eqn. 175
    for (auto const &ommer : block.ommers) {
        auto const ommer_reward = calculate_ommer_reward(
            block_reward, block.header.number, ommer.number);
        if (MONAD_LIKELY(ommer_reward)) {
            state.add_to_balance(ommer.beneficiary, ommer_reward);
        }
    }

    MONAD_DEBUG_ASSERT(block_state.can_merge(state.state_));
    block_state.merge(state.state_);
}

MONAD_NAMESPACE_END
