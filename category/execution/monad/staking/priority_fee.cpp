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
#include <category/core/log.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/staking/priority_fee.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/staking_error.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

void collect_priority_fee(State &state, uint256_t const &fee)
{
    state.add_to_balance(PRIORITY_FEE_DIST_ADDRESS, fee);
}

void distribute_priority_fees(State &state)
{
    uint256_t const fees = state.get_balance(PRIORITY_FEE_DIST_ADDRESS);
    if (fees == 0) {
        return;
    }

    // Drain unconditionally: the subtract is outside the push/pop, so a
    // failed distribution burns the fees rather than leaving them in the
    // dist address.
    state.subtract_from_balance(PRIORITY_FEE_DIST_ADDRESS, fees);

    state.push();
    state.add_to_balance(STAKING_CA, fees);
    NoopCallTracer call_tracer;
    StakingContract contract(state, call_tracer);
    auto const res = contract.distribute_priority_fees(fees);
    if (res.has_error()) {
        auto const error_message = res.error().message();
        LOG_WARNING(
            "staking: distribute priority fee reverted: {}",
            std::string{error_message.data(), error_message.size()});
        // At the start of block execution, the proposer id is always cleared to
        // 0 and is set by the reward syscall. If the reward syscall was not
        // included, `UnknownValidator` will be returned, and that is the only
        // state we permit.
        MONAD_ASSERT_THROW(
            res.error() == StakingError::UnknownValidator,
            "fee distribution error");
        state.pop_reject();
    }
    else {
        state.pop_accept();
    }
}

MONAD_STAKING_NAMESPACE_END
