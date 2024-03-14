#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct Chain
{
    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision get_revision(BlockHeader const &) const = 0;
};

MONAD_NAMESPACE_END
