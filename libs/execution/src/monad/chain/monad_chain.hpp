#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct MonadChain : Chain
{
    Result<void> validate_header(
        std::vector<Receipt> const &, BlockHeader const &) const override;

    virtual bool validate_root(
        evmc_revision, BlockHeader const &, bytes32_t const &state_root,
        bytes32_t const &receipts_root, bytes32_t const &transactions_root,
        std::optional<bytes32_t> const &withdrawals_root) const override;
};

MONAD_NAMESPACE_END
