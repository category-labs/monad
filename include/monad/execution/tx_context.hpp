#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>

#include <evmc/evmc.h>

#include <cstdint>

static_assert(sizeof(evmc_tx_context) == 192);
static_assert(alignof(evmc_tx_context) == 8);

MONAD_NAMESPACE_BEGIN

template <class Traits>
constexpr evmc_tx_context
get_tx_context(Transaction const &tx, BlockHeader const &hdr)
{
    return {
        .tx_gas_price = to_bytes(to_big_endian(execution::gas_price<Traits>(
            tx, hdr.base_fee_per_gas.value_or(0)))),
        .tx_origin = tx.from.value(),
        .block_coinbase = hdr.beneficiary,
        .block_number = static_cast<int64_t>(hdr.number),
        .block_timestamp = static_cast<int64_t>(hdr.timestamp),
        .block_gas_limit = static_cast<int64_t>(hdr.gas_limit),
        .block_prev_randao = hdr.difficulty
                                 ? to_bytes(to_big_endian(hdr.difficulty))
                                 : hdr.prev_randao,
        .chain_id = to_bytes(to_big_endian(uint256_t{1})), // TODO
        .block_base_fee =
            to_bytes(to_big_endian(hdr.base_fee_per_gas.value_or(0)))};
}

MONAD_NAMESPACE_END
