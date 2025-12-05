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

#include <category/core/likely.h>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/staking/execute_block_prelude.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

template <Traits traits>
void execute_block_prelude(State &state)
{
    if constexpr (traits::monad_rev() < MONAD_FIVE) {
        return;
    }

    if (MONAD_UNLIKELY(!state.account_exists(STAKING_CA))) {
        return;
    }

    // pessimistically clear the proposer id slot in the case no reward txn is
    // included with this block.
    NoopCallTracer call_tracer;
    StakingContract contract(state, call_tracer);
    contract.vars.proposer_val_id.clear();
}

EXPLICIT_MONAD_TRAITS(execute_block_prelude);

MONAD_STAKING_NAMESPACE_END
