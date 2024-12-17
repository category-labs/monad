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

    virtual Result<void> validate_header(
        std::vector<Receipt> const &, BlockHeader const &) const = 0;

    virtual bool validate_root(
        evmc_revision, BlockHeader const &, bytes32_t const &state_root,
        bytes32_t const &receipts_root, bytes32_t const &transactions_root,
        std::optional<bytes32_t> const &withdrawals_root) const = 0;
};

MONAD_NAMESPACE_END
