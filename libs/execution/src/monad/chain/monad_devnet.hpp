#pragma once

#include <monad/chain/genesis_state.hpp>
#include <monad/chain/monad_chain.hpp>
#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct MonadDevnet : MonadChain
{
    using MonadChain::MonadChain;

    virtual monad_revision get_monad_revision() const override;

    virtual uint256_t get_chain_id() const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
