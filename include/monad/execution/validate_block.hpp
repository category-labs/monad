#pragma once

#include <monad/config.hpp>
#include <monad/execution/validation_status.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct Block;
struct BlockHeader;

template <evmc_revision rev>
ValidationStatus static_validate_header(BlockHeader const &);

template <evmc_revision rev>
ValidationStatus static_validate_block(Block const &);

MONAD_NAMESPACE_END
