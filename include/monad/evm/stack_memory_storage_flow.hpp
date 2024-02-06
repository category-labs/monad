#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/system_state.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// inline Status mload(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const &offset = sp.pop();
//
//     BOOST_OUTCOME_TRY(
//         auto const grow_cost,
//         state.memory.grow_if_needed(
//             state.mstate.gas_left, offset, sizeof(uint256_t)));
//
//     state.mstate.gas_left -= grow_cost;
//
//     MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
//     auto const dst =
//         state.memory.substr(static_cast<size_t>(offset), sizeof(uint256_t));
//     sp.push(intx::be::unsafe::load<uint256>(dst.data()));
//     return Status::Success;
// }
//
// inline Status mstore(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const &offset = stack.pop();
//     auto const &value = stack.pop();
//
//     BOOST_OUTCOME_TRY(
//         auto const grow_cost,
//         state.memory.grow_if_needed(
//             state.mstate.gas_left, offset, sizeof(uint256_t)));
//
//     state.mstate.gas_left -= grow_cost;
//
//     MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
//     auto const dst =
//         state.memory.substr(static_cast<size_t>(offset), sizeof(uint256_t));
//     intx::be::unsafe::store(dst.data(), value);
//     return Status::Success;
// }
//
// inline Result
// mstore8(StackTop stack, int64_t gas_left, ExecutionState &state) noexcept
//{
//     auto const &offset = stack.pop();
//     auto const &value = stack.pop();
//
//     BOOST_OUTCOME_TRY(
//         auto const grow_cost,
//         state.memory.grow_if_needed(
//             state.mstate.gas_left, offset, sizeof(uint256_t)));
//
//     state.mstate.gas_left -= grow_cost;
//
//     MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
//     auto dst =
//         state.memory.substr(static_cast<size_t>(offset), sizeof(uint8_t));
//
//     MONAD_ASSERT(value <= std::numeric_limits<uint8_t>::max());
//     dst[0] = static_cast<uint8_t>(value);
//     return Result::Success;
// }
//
// template <Revision rev>
// Status sload(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const key = intx::be::store<evmc::bytes32>(sp.pop());
//
//     if (rev >= EVMC_BERLIN &&
//         state.sstate.access_storage(state.env.address, key) ==
//             AccessStatus::Cold) {
//         if (gas_left < additional_cold_sload_cost) {
//             return Status::OutOfGas;
//         }
//         state.mstate.gas_left -= additional_cold_sload_cost;
//     }
//
//     sp.push(intx::be::load<uint256>(
//         state.sstate.get_storage(state.env.address, key)));
//
//     return Status::Success;
// }
//
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

// inline Result<byte_string::const_iterator>
// jump_impl(ExecutionState const &state, uint256_t const &counter) noexcept
//{
//     auto const &is_jump_dest = state.analysis.is_jump_dest;
//     if (counter >= is_jump_dest.size() ||
//         !is_jump_dest.at(static_cast<size_t>(counter))) {
//         return Status::BadJumpDest;
//     }
//
//     MONAD_ASSERT(counter <= std::numeric_limits<size_t>::max());
//     return &state.analysis.code.at(static_cast<size_t>(counter));
// }
//
// inline Result<byte_string::const_iterator>
// jump(StackPointer sp, ExecutionState const &state) noexcept
//{
//     return jump_impl(state, sp.pop());
// }
//
// inline Result<byte_string::const_iterator>
// jumpi(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const &counter = sp.pop();
//     auto const &b = sp.pop();
//     return b ? jump_impl(state, counter) : state.mstate.pc + 1;
// }
//
// inline void pc(StackPointer sp, ExecutionState const &state) noexcept
//{
//     MONAD_ASSERT(state.mstate.pc >= state.analysis.code.begin());
//     sp.push(
//         static_cast<uint64_t>(state.mstate.pc -
//         state.analysis.code.begin()));
// }
//
// inline void msize(StackPointer sp, ExecutionState const &state) noexcept
//{
//     sp.push(state.mstate.memory.size());
// }
//
// inline void gas(StackPointer sp, ExecutionState const &state) noexcept
//{
//     sp.push(gas_left.mstate.gas_left);
// }

MONAD_EVM_NAMESPACE_END
