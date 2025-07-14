#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
evmc_tx_context get_tx_context(
    Transaction const &tx, Address const &sender, BlockHeader const &hdr,
    uint256_t const &chain_id)
{
    return {
        .tx_gas_price = to_bytes(to_big_endian(
            gas_price<rev>(tx, hdr.base_fee_per_gas.value_or(0)))),
        .tx_origin = sender,
        .block_coinbase = hdr.beneficiary,
        .block_number = static_cast<int64_t>(hdr.number),
        .block_timestamp = static_cast<int64_t>(hdr.timestamp),
        .block_gas_limit = static_cast<int64_t>(hdr.gas_limit),
        .block_prev_randao = hdr.difficulty
                                 ? to_bytes(to_big_endian(hdr.difficulty))
                                 : hdr.prev_randao,
        .chain_id = to_bytes(to_big_endian(chain_id)),
        .block_base_fee =
            to_bytes(to_big_endian(hdr.base_fee_per_gas.value_or(0))),
        .blob_base_fee{}, // TODO
        .blob_hashes = nullptr, // TODO
        .blob_hashes_count = 0, // TODO
        .initcodes = nullptr, // TODO
        .initcodes_count = 0, // TODO
    };
}

EXPLICIT_EVMC_REVISION(get_tx_context);

MONAD_NAMESPACE_END
