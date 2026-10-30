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

#include <category/execution/ethereum/block_hash_history.hpp>

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Note: EIP-2935 says the get on the block hash history contract should revert
// if the block number is outside of the block history. However, current usage
// of this function guarantees that it is always valid.
bytes32_t get_block_hash_history(State &state, uint64_t const block_number)
{
    if (MONAD_UNLIKELY(
            state.get_code_hash(BLOCK_HISTORY_ADDRESS) !=
            BLOCK_HISTORY_CODE_HASH)) {
        return bytes32_t{};
    }

    uint256_t const index{block_number % BLOCK_HISTORY_LENGTH};
    return state.get_storage(
        BLOCK_HISTORY_ADDRESS, store_be_as<bytes32_t>(index));
}

MONAD_NAMESPACE_END
