// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/explicit_evm_chain.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/vm/evm/chain.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
evmc_tx_context get_tx_context(
    Transaction const &tx, Address const &sender, BlockHeader const &hdr,
    uint256_t const &chain_id)
{
    return {
        .tx_gas_price = to_bytes(to_big_endian(
            gas_price<traits>(tx, hdr.base_fee_per_gas.value_or(0)))),
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
        .blob_base_fee = to_bytes(to_big_endian(
            get_base_fee_per_blob_gas(hdr.excess_blob_gas.value_or(0)))),
        .blob_hashes = tx.blob_versioned_hashes.data(),
        .blob_hashes_count = tx.blob_versioned_hashes.size(),
        .initcodes = nullptr, // TODO
        .initcodes_count = 0, // TODO
    };
}

EXPLICIT_EVM_CHAIN(get_tx_context);

MONAD_NAMESPACE_END
