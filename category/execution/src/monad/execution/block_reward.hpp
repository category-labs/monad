#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct Block;
class State;

template <evmc_revision rev>
void apply_block_reward(State &, Block const &);

MONAD_NAMESPACE_END
