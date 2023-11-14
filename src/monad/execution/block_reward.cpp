#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/db/db.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>

MONAD_NAMESPACE_BEGIN

constexpr uint256_t calculate_block_reward(
    Block const &block, uint256_t const &reward, uint256_t const &ommer_reward)
{
    MONAD_DEBUG_ASSERT(
        reward + intx::umul(ommer_reward, uint256_t{block.ommers.size()}) <=
        std::numeric_limits<uint256_t>::max());
    return reward + ommer_reward * block.ommers.size();
}

constexpr uint256_t const calculate_ommer_reward(
    Block const &block, uint256_t const &reward, uint64_t ommer_number)
{
    auto const subtrahend = ((block.header.number - ommer_number) * reward) / 8;
    return reward - subtrahend;
}

void apply_block_reward(
    BlockState &block_state, Db &db, Block const &block,
    uint256_t const &block_reward, uint256_t const &ommer_reward)
{
    State state{block_state, db};
    auto const miner_reward =
        calculate_block_reward(block, block_reward, ommer_reward);

    // reward block beneficiary, YP Eqn. 172
    if (MONAD_LIKELY(miner_reward)) {
        state.add_to_balance(block.header.beneficiary, miner_reward);
    }

    // reward ommers, YP Eqn. 175
    for (auto const &header : block.ommers) {
        auto const ommer_reward =
            calculate_ommer_reward(block, block_reward, header.number);
        if (MONAD_LIKELY(ommer_reward)) {
            state.add_to_balance(header.beneficiary, ommer_reward);
        }
    }
    MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
    merge(block_state.state, state.state_);
}

MONAD_NAMESPACE_END
