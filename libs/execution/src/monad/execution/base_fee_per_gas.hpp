#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t base_fee_per_gas(BlockHeader const &);

MONAD_NAMESPACE_END
