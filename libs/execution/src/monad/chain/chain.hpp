#pragma once

#include <monad/chain/genesis_state.hpp>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;
struct Transaction;

class Chain
{
protected:
    uint64_t block_number_{0};
    uint64_t timestamp_{0};

public:
    Chain() = default;
    Chain(uint64_t block_number, uint64_t timestamp);
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision get_revision() const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const = 0;

    virtual uint64_t compute_gas_refund(
        Transaction const &, uint64_t gas_remaining, uint64_t refund) const = 0;

    virtual size_t get_max_code_size() const = 0;

    virtual GenesisState get_genesis_state() const = 0;
};

MONAD_NAMESPACE_END
