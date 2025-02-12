#pragma once

#include <monad/chain/chain.hpp>
#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Transaction;

struct MonadChain : Chain
{
    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const override;

    virtual monad_revision
    get_monad_revision(uint64_t block_number, uint64_t timestamp) const = 0;
};

MONAD_NAMESPACE_END
