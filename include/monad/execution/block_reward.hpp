#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockState;

void apply_block_reward(
    BlockState &, Block const &, uint256_t const &block_reward,
    uint256_t const &ommer_reward);

MONAD_NAMESPACE_END
