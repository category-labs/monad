#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
evmc_tx_context get_tx_context(Transaction const &tx, BlockHeader const &hdr)
{
    MONAD_DEBUG_ASSERT(tx.from.has_value());

    return {
        .tx_gas_price = to_bytes(to_big_endian(
            gas_price<rev>(tx, hdr.base_fee_per_gas.value_or(0)))),
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

EXPLICIT_EVMC_REVISION(get_tx_context);

MONAD_NAMESPACE_END
