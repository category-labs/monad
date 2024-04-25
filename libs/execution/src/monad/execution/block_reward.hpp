#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockState;

template <evmc_revision rev>
void apply_block_reward(BlockState &, Block const &);

MONAD_NAMESPACE_END
