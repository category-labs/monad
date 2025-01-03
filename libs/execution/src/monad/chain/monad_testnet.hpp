#pragma once

#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct MonadTestnet : MonadChain
{
    virtual uint256_t get_chain_id() const override;

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;
};

MONAD_NAMESPACE_END
