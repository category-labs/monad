#pragma once

#include <monad/chain/monad_chain.hpp>
#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct MonadDevnet : MonadChain
{
    virtual monad_revision get_monad_revision(
        uint64_t block_number, uint64_t timestamp) const override;

    virtual uint256_t get_chain_id() const override;
};

MONAD_NAMESPACE_END
