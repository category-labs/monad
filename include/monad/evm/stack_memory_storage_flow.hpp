#pragma once

#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
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
struct Trait<Opcode::MLOAD>
{
    static constexpr size_t stack_height_required = 1;
    static constexpr int stack_height_change = 0;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState &state) noexcept
    {
        auto const &offset = sp.pop();

        if (auto const status = state.mstate.memory.grow_if_needed(
                state.mstate.gas_left, offset, sizeof(uint256_t));
            status != Status::Success) {
            return status;
        }

        MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
        auto const dst = state.mstate.memory.substr(
            static_cast<size_t>(offset), sizeof(uint256_t));
        sp.push(intx::be::unsafe::load<uint256_t>(dst.data()));
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
    }
};

template <>
struct Trait<Opcode::MSTORE>
{
    static constexpr size_t stack_height_required = 2;
    static constexpr int stack_height_change = -2;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState &state)
    {
        auto const &offset = sp.pop();
        auto const &value = sp.pop();

        if (auto const status = state.mstate.memory.grow_if_needed(
                state.mstate.gas_left, offset, sizeof(uint256_t));
            status != Status::Success) {
            return status;
        }

        MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());

        auto const bytes = intx::be::store<bytes32_t>(value);
        state.mstate.memory.replace(
            static_cast<size_t>(offset),
            sizeof(uint256_t),
            byte_string_view{bytes.bytes, sizeof(bytes32_t)});
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return very_low_cost;
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

template <>
struct Trait<Opcode::GAS>
{
    static constexpr size_t stack_height_required = 0;
    static constexpr int stack_height_change = 1;
    static constexpr size_t pc_increment = 1;
    static constexpr Revision since = Revision::Frontier;

    template <Revision>
    static Status impl(StackPointer sp, ExecutionState const &state)
    {
        sp.push(state.mstate.gas_left);
        return Status::Success;
    }

    template <Revision>
    static constexpr uint64_t baseline_cost()
    {
        return base_cost;
    }
};

MONAD_EVM_NAMESPACE_END
