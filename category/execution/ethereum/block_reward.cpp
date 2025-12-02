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
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
constexpr uint256_t block_reward()
{
    if constexpr (traits::evm_rev() < EVMC_BYZANTIUM) {
        return 5'000'000'000'000'000'000; // YP Eqn. 176
    }
    else if constexpr (traits::evm_rev() < EVMC_PETERSBURG) {
        return 3'000'000'000'000'000'000; // YP Eqn. 176, EIP-649
    }
    else if constexpr (traits::evm_rev() < EVMC_PARIS) {
        return 2'000'000'000'000'000'000; // YP Eqn. 176, EIP-1234
    }
    return 0; // EIP-3675
}

template <Traits traits>
constexpr uint256_t additional_ommer_reward()
{
    return block_reward<traits>() >> 5; // YP Eqn. 172, block reward / 32
}

constexpr uint256_t calculate_block_reward(
    uint256_t const &reward, uint256_t const &ommer_reward,
    size_t const ommers_size)
{
    MONAD_ASSERT(
        intx::umul(ommer_reward, uint256_t{ommers_size}) <=
        std::numeric_limits<uint256_t>::max() - reward);

    return reward + ommer_reward * ommers_size;
}

constexpr uint256_t const calculate_ommer_reward(
    uint256_t const &reward, uint64_t const header_number,
    uint64_t const ommer_number)
{
    auto const subtrahend = ((header_number - ommer_number) * reward) / 8;
    return reward - subtrahend;
}

template <Traits traits>
void apply_block_reward(State &state, InputBlock const block)
{
    auto const miner_reward = calculate_block_reward(
        block_reward<traits>(),
        additional_ommer_reward<traits>(),
        block.ommers.size());

    // reward block beneficiary, YP Eqn. 172
    if (MONAD_LIKELY(miner_reward)) {
        state.add_to_balance(block.header_inputs.beneficiary, miner_reward);
    }

    // reward ommers, YP Eqn. 175
    for (auto const &ommer : block.ommers) {
        auto const ommer_reward = calculate_ommer_reward(
            block_reward<traits>(),
            block.header_inputs.number,
            ommer.number);
        if (MONAD_LIKELY(ommer_reward)) {
            state.add_to_balance(ommer.beneficiary, ommer_reward);
        }
    }
}

EXPLICIT_TRAITS(apply_block_reward);

MONAD_NAMESPACE_END
