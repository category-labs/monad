#pragma once

#include <monad/chain/genesis_state.hpp>
#include <monad/chain/monad_chain.hpp>
#include <monad/chain/monad_revision.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct MonadTestnet2 : MonadChain
{
    virtual monad_revision get_monad_revision(
        uint64_t block_number, uint64_t timestamp) const override;

    virtual uint256_t get_chain_id() const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
