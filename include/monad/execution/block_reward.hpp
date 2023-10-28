#pragma once

#include <monad/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>

#include <monad/db/db.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

MONAD_NAMESPACE_BEGIN

[[nodiscard]] constexpr uint256_t calculate_block_reward(
    Block const &block, uint256_t const &reward, uint256_t const &ommer_reward)
{
    MONAD_DEBUG_ASSERT(
        reward + intx::umul(ommer_reward, uint256_t{block.ommers.size()}) <=
        std::numeric_limits<uint256_t>::max());
    return reward + ommer_reward * block.ommers.size();
}

[[nodiscard]] constexpr uint256_t const calculate_ommer_reward(
    Block const &block, uint256_t const &reward, uint64_t ommer_number)
{
    auto const subtrahend = ((block.header.number - ommer_number) * reward) / 8;
    return reward - subtrahend;
}

void apply_block_reward(
    BlockState &, Db &, Block const &, uint256_t const &block_reward,
    uint256_t const &ommer_reward);

MONAD_NAMESPACE_END
