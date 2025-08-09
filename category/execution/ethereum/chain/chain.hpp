#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>

#include <evmc/evmc.h>

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

    virtual GenesisState get_genesis_state() const = 0;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, uint64_t i,
        Transaction const &, Address const &sender, State &,
        void *chain_context) const = 0;

    virtual bool revert_transaction(
        uint64_t block_number, uint64_t timestamp, uint64_t i, Address const &,
        State const &, void *chain_context) const;
};

MONAD_NAMESPACE_END
