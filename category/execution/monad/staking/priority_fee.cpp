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

#include <category/core/int.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/staking/priority_fee.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <algorithm>

MONAD_STAKING_NAMESPACE_BEGIN

template <Traits traits>
void collect_priority_fee(
    State &state, BlockHeader const &header, uint256_t const &fee)
{
    if constexpr (traits::monad_rev() >= MONAD_NEXT) {
        state.add_to_balance(PRIORITY_FEE_DIST_ADDRESS, fee);
    }
    else {
        state.add_to_balance(header.beneficiary, fee);
    }
}

template <Traits traits>
void distribute_priority_fees(State &state)
{
    if constexpr (traits::monad_rev() < MONAD_NEXT) {
        return;
    }

    uint256_t const priority_fees_this_block =
        state.get_balance(PRIORITY_FEE_DIST_ADDRESS);
    if (priority_fees_this_block == 0) {
        return;
    }

    // Drain the dist address unconditionally.  Failed distributions burn the
    // fees. In practice, this only can happen when the fee is below the staking
    // dust threshold, or if the proposer is not in the valset.
    state.subtract_from_balance(
        PRIORITY_FEE_DIST_ADDRESS, priority_fees_this_block);

    NoopCallTracer call_tracer;
    StakingContract contract(state, call_tracer);

    uint256_t remaining = priority_fees_this_block;
    while (remaining > 0) {
        uint256_t const chunk =
            std::min(remaining, limits::max_external_reward());
        // Push/pop per chunk so a failed chunk doesn't undo prior ones.
        state.push();
        state.add_to_balance(STAKING_CA, chunk);
        auto const val_id = contract.vars.proposer_val_id.load();
        auto const res = contract.apply_external_reward(
            val_id,
            PRIORITY_FEE_DIST_ADDRESS,
            chunk,
            /* apply_commission */ true);
        if (res.has_error()) {
            state.pop_reject();
        }
        else {
            state.pop_accept();
        }
        remaining -= chunk;
    }
}

EXPLICIT_MONAD_TRAITS(collect_priority_fee);
EXPLICIT_MONAD_TRAITS(distribute_priority_fees);

MONAD_STAKING_NAMESPACE_END
