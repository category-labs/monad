#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct MonadChain : Chain
{
    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;
};

MONAD_NAMESPACE_END
