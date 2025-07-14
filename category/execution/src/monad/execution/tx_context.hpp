#pragma once

#include <category/core/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>

static_assert(sizeof(evmc_tx_context) == 256);
static_assert(alignof(evmc_tx_context) == 8);

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Transaction;

inline constexpr evmc_tx_context EMPTY_TX_CONTEXT{
    .tx_gas_price{},
    .tx_origin{},
    .block_coinbase{},
    .block_number = 0,
    .block_timestamp = 0,
    .block_gas_limit = 0,
    .block_prev_randao{},
    .chain_id{},
    .block_base_fee{},
    .blob_base_fee{},
    .blob_hashes = nullptr,
    .blob_hashes_count = 0,
    .initcodes = nullptr,
    .initcodes_count = 0};

template <evmc_revision rev>
evmc_tx_context get_tx_context(
    Transaction const &, Address const &sender, BlockHeader const &,
    uint256_t const &chain_id);

MONAD_NAMESPACE_END
