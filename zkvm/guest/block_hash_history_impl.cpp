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

// The guest's EIP-2935 history read, in place of the host's
// block_hash_history_impl.cpp. Deliberately tolerant of an incomplete
// witness; do not make it strict.
//
// reth builds a witness from the state its own execution touched, and revm
// answers BLOCKHASH from the node's header store rather than by reading the
// history contract. The only thing that touches the contract during a block
// is the prologue, which writes the parent's slot. So a reth witness proves
// the history account and at most that one slot, and a BLOCKHASH for any
// older block finds its slot unproven. That is a gap in the witness, not a
// proven zero: the read answers zero and StateHostBase::get_block_hash falls
// back to the WitnessBlockHashBuffer, whose hashes are authenticated through
// the parent-hash chain.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

bytes32_t get_block_hash_history(State &state, uint64_t const block_number)
{
    if (MONAD_UNLIKELY(
            state.get_code_hash(BLOCK_HISTORY_ADDRESS) !=
            BLOCK_HISTORY_CODE_HASH)) {
        return bytes32_t{};
    }

    uint256_t const index{block_number % BLOCK_HISTORY_LENGTH};
    return state
        .try_get_storage(BLOCK_HISTORY_ADDRESS, store_be_as<bytes32_t>(index))
        .value_or(bytes32_t{});
}

MONAD_NAMESPACE_END
