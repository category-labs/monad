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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <evmc/evmc.h>
#include <evmc/hex.hpp>

#include <cstdint>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

byte_string const BLOCK_HISTORY_CODE =
    evmc::from_hex(
        "0x3373fffffffffffffffffffffffffffffffffffffffe14604657602036036042575f"
        "35600143038111604257611fff81430311604257611fff9006545f5260205ff35b5f5f"
        "fd5b5f35611fff60014303065500")
        .value();

constexpr auto BLOCK_HISTORY_CODE_HASH{
    0x6e49e66782037c0555897870e29fa5e552daf4719552131a0abce779daec0a5d_bytes32};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
void deploy_block_hash_history_contract(State &state)
{
    if constexpr (traits::evm_rev() < EVMC_PRAGUE) {
        return;
    }

    // happy path: deploy contract if it doesn't exist
    if (MONAD_UNLIKELY(!state.account_exists(BLOCK_HISTORY_ADDRESS))) {
        state.create_contract(BLOCK_HISTORY_ADDRESS);
        state.set_code(BLOCK_HISTORY_ADDRESS, BLOCK_HISTORY_CODE);
        MONAD_ASSERT(
            state.get_code_hash(BLOCK_HISTORY_ADDRESS) ==
            BLOCK_HISTORY_CODE_HASH);
        state.set_nonce(BLOCK_HISTORY_ADDRESS, 1);
    }

    // cleanup: overwrite bad code from MONAD_FOUR
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
    if constexpr (traits::evm_rev() < EVMC_PRAGUE) {
        return;
    }

    // before MONAD_SIX, nothing was being written.
    if constexpr (is_monad_trait_v<traits>) {
        if constexpr (traits::monad_rev() < MONAD_SIX) {
            return;
        }
    }

    if (MONAD_UNLIKELY(!header.number)) {
        return;
    }

    if (MONAD_LIKELY(state.account_exists(BLOCK_HISTORY_ADDRESS))) {
        uint64_t const parent_number = header.number - 1;
        uint256_t const index{parent_number % BLOCK_HISTORY_LENGTH};
        bytes32_t const key{to_bytes(to_big_endian(index))};
        state.set_storage(BLOCK_HISTORY_ADDRESS, key, header.parent_hash);
    }
}

EXPLICIT_TRAITS(set_block_hash_history);

// Note: EIP-2935 says the get on the block hash history contract should revert
// if the block number is outside of the block history. However, current usage
// of this function guarantees that it is always valid.
bytes32_t get_block_hash_history(State &state, uint64_t const block_number)
{
    if (MONAD_UNLIKELY(!state.account_exists(BLOCK_HISTORY_ADDRESS))) {
        return bytes32_t{};
    }

    uint256_t const index{block_number % BLOCK_HISTORY_LENGTH};
    return state.get_storage(
        BLOCK_HISTORY_ADDRESS, to_bytes(to_big_endian(index)));
}

MONAD_NAMESPACE_END
