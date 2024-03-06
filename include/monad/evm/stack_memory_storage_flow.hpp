#pragma once

#include <monad/core/assert.h>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/trait.hpp>

MONAD_EVM_NAMESPACE_BEGIN

template <>
struct Trait<Opcode::POP>
{
    static constexpr size_t stack_height_required = 1;
    static constexpr int stack_height_change = -1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer const &, ExecutionState &)
    {
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

template <>
struct Trait<Opcode::SSTORE>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -2;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision rev>
    static Status impl(StackPointer sp, ExecutionState &state)
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
        auto const status =
            state.sstate.set_storage(state.env.address, key, value);

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

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return zero_cost;
    }
};

template <>
struct Trait<Opcode::PC>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        MONAD_ASSERT(state.mstate.pc >= 0);
        sp.push(state.mstate.pc);
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

MONAD_EVM_NAMESPACE_END
