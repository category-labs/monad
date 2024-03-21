#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct EthereumMainnet : Chain
{
    virtual uint256_t get_chain_id() const override;

    virtual evmc_revision get_revision(BlockHeader const &) const override;

    virtual Result<void>
    static_validate_header(BlockHeader const &) const override;
};

MONAD_NAMESPACE_END
