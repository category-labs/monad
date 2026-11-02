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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_ANONYMOUS_NAMESPACE_BEGIN
byte_string const BLOCK_HISTORY_CODE =
    from_hex(
        "0x3373fffffffffffffffffffffffffffffffffffffffe14604657602036036042575f"
        "35600143038111604257611fff81430311604257611fff9006545f5260205ff35b5f5f"
        "fd5b5f35611fff60014303065500")
        .value();

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
void deploy_block_hash_history_contract(State &state)
{
    if constexpr (!traits::eip_2935_active()) {
        return;
    }

    // happy path: deploy contract if it doesn't exist
    if (MONAD_UNLIKELY(
            !state.account_has_code_or_nonce(BLOCK_HISTORY_ADDRESS))) {
        state.create_contract(BLOCK_HISTORY_ADDRESS);
        state.set_code(BLOCK_HISTORY_ADDRESS, BLOCK_HISTORY_CODE);
        MONAD_ASSERT(
            state.get_code_hash(BLOCK_HISTORY_ADDRESS) ==
            BLOCK_HISTORY_CODE_HASH);
        state.set_nonce(BLOCK_HISTORY_ADDRESS, 1);
    }

    // Monad-only workaround, not a feature: MONAD_FOUR deployed bad code and
    // MONAD_SIX overwrites it, so this compares the revision directly.
    if constexpr (is_monad_trait_v<traits>) {
        if constexpr (traits::monad_rev() >= MONAD_SIX) {
            if (MONAD_UNLIKELY(
                    state.get_code_hash(BLOCK_HISTORY_ADDRESS) !=
                    BLOCK_HISTORY_CODE_HASH)) {
                state.set_code(BLOCK_HISTORY_ADDRESS, BLOCK_HISTORY_CODE);
            }
        }
    }
}

EXPLICIT_TRAITS(deploy_block_hash_history_contract);

template <Traits traits>
void set_block_hash_history(State &state, BlockHeader const &header)
{
    if constexpr (!traits::eip_2935_active()) {
        return;
    }

    if constexpr (is_monad_trait_v<traits>) {
        if constexpr (traits::monad_rev() < MONAD_SIX) {
            return;
        }
    }

    if (MONAD_UNLIKELY(!header.number)) {
        return;
    }

    if (MONAD_LIKELY(
            state.get_code_hash(BLOCK_HISTORY_ADDRESS) ==
            BLOCK_HISTORY_CODE_HASH)) {
        uint64_t const parent_number = header.number - 1;
        uint256_t const index{parent_number % BLOCK_HISTORY_LENGTH};
        bytes32_t const key{store_be_as<bytes32_t>(index)};
        state.set_storage(BLOCK_HISTORY_ADDRESS, key, header.parent_hash);
    }
}

EXPLICIT_TRAITS(set_block_hash_history);

// Note: EIP-2935 says the get on the block hash history contract should revert
// if the block number is outside of the block history. However, current usage
// of this function guarantees that it is always valid.
//
// Deliberately tolerant of an incomplete witness; do not make it strict.
//
// reth builds a witness from the state its own execution touched, and revm
// answers BLOCKHASH from the node's header store rather than by reading the
// EIP-2935 history contract. The only thing that touches the contract during
// a block is the prelude system call, which writes the parent's slot. So a
// reth witness proves the history account and at most that one slot, and a
// BLOCKHASH for any older block finds its slot absent. That absence is a gap
// in the witness, not a proven zero, so this returns zero and the caller
// (EvmcHostBase::get_block_hash) falls back to the block hash buffer, whose
// hashes the guest authenticates through the parent-hash chain. The native
// state resolves everything, so for it this is the strict read.
bytes32_t get_block_hash_history(State &state, uint64_t const block_number)
{
    uint256_t const index{block_number % BLOCK_HISTORY_LENGTH};
    bytes32_t const key{store_be_as<bytes32_t>(index)};
    // A present value implies the history account is resolved, so the code
    // hash can be read afterwards without tripping the resolution assert.
    auto const value = state.try_get_storage(BLOCK_HISTORY_ADDRESS, key);
    if (MONAD_UNLIKELY(
            !value || state.get_code_hash(BLOCK_HISTORY_ADDRESS) !=
                          BLOCK_HISTORY_CODE_HASH)) {
        return bytes32_t{};
    }
    return *value;
}

MONAD_NAMESPACE_END
