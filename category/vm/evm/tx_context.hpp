// Copyright (C) 2025-26 Category Labs, Inc.
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

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>

#include <cstddef>
#include <cstdint>

namespace monad::vm
{
    // Mirrors evmc_tx_context field-for-field, including the category-labs
    // fork's block_round; layout equality is asserted in tx_context.cpp.
    struct TxContext
    {
        bytes32_t tx_gas_price;
        Address tx_origin;
        Address block_coinbase;
        int64_t block_number;
        int64_t block_timestamp;
        int64_t block_gas_limit;
        bytes32_t block_prev_randao;
        bytes32_t chain_id;
        bytes32_t block_base_fee;
        bytes32_t blob_base_fee;
        bytes32_t const *blob_hashes;
        size_t blob_hashes_count;
        // EOF TXCREATE initcodes: never populated; kept for evmc layout parity.
        void const *initcodes;
        size_t initcodes_count;
        uint64_t block_round;
    };
}
