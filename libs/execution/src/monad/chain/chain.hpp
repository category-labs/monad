#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision
    get_revision(uint64_t block_header, uint64_t timestamp) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const = 0;
};

MONAD_NAMESPACE_END
