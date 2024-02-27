#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <Revision rev>
Status sstore(StackPointer sp, ExecutionState &state)
{
    if (!state.env.can_modify_state) {
        return Status::StaticModeViolation;
    }

    // protection against re-entrancy attacks introduced with EIP-1283 (read
    // EIP-2200)
    if (rev >= Revision::Istanbul && state.mstate.gas_left <= 2300) {
        return Status::OutOfGas;
    }

    auto const key = intx::be::store<bytes32_t>(sp.pop());
    auto const value = intx::be::store<bytes32_t>(sp.pop());

    auto const gas_cost_cold = [&] {
        if constexpr (rev >= Revision::Berlin) {
            return state.sstate.access_storage(state.env.address, key)
                       ? 0
                       : cold_sload_cost<rev>();
        }
        else {
            return 0;
        }
    }();
    MONAD_ASSERT(state.mstate.gas_left >= gas_cost_cold);
    auto const status = state.sstate.set_storage(state.env.address, key, value);

    auto const cost = sstore_cost<rev>(status);
    auto const refund = sstore_refund<rev>(status);
    auto const gas_cost = cost + gas_cost_cold;
    if (state.mstate.gas_left < gas_cost) {
        return Status::OutOfGas;
    }
    state.mstate.gas_left -= gas_cost;
    state.gas_refund += refund;
    return Status::Success;
}

MONAD_EVM_NAMESPACE_END
