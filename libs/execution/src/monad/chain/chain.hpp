#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

class State;
struct BlockHeader;
struct Receipt;
struct Transaction;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const = 0;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const = 0;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual std::optional<evmc::Result> try_execute_precompile(
        State &, evmc_message const &, evmc_revision) const = 0;
};

MONAD_NAMESPACE_END
