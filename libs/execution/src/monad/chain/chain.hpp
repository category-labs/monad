#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct Chain
{
    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision get_revision(BlockHeader const &) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual bool validate_root(
        evmc_revision, BlockHeader const &, bytes32_t const &state_root,
        bytes32_t const &receipts_root) const = 0;
};

MONAD_NAMESPACE_END
