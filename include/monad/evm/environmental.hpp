#pragma once

#include <monad/core/int.hpp>
#include <monad/core/result.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// void copy_impl2(
//     MachineState &mstate, byte_string_view const input,
//     size_t const dest_offset, uint256_t const &offset, size_t const size)
//{
//     auto dst = mstate.memory.substr(dest_offset, size);
//
//     auto const copy_size =
//         std::min(size, input.size() - std::min(input.size(), offset));
//     if (copy_size) {
//         std::copy_n(input.data(), copy_size, dst.data());
//     }
//
//     if (size > copy_size) {
//         std::fill_n(dst.data() + copy_size, size - copy_size, 0);
//     }
// }
//
// Result<uint64_t> copy_impl(
//     MachineState &mstate, byte_string_view const input,
//     uint256_t const &dest_offset, uint256_t const &offset,
//     uint256_t const &size)
//{
//     if (size == 0) {
//         return 0;
//     }
//
//     BOOST_OUTOME_TRY(
//         auto const grow_cost,
//         mstate.memory.grow_if_needed(mstate.gas_left, dest_offset, size));
//     MONAD_ASSERT(grow_cost <= mstate.gas_left);
//     MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());
//     MONAD_ASSERT(dest_offset <= std::numeric_limits<size_t>::max());
//
//     auto const cost = copy_cost(size);
//
//     if ((cost + grow_cost) > mstate.gas_left) {
//         return Status::OutOfGas;
//     }
//
//     copy_impl2(
//         grow_cost,
//         mstate,
//         input,
//         static_cast<size_t>(dest_offset),
//         offset,
//         static_cast<size_t>(size));
//
//     return cost + grow_cost;
// }
//
//[[gnu::always_inline]] inline void
// address(StackPointer sp, ExecutionEnvironment const &env) noexcept
//{
//     sp.push(intx::be::load<uint256_t>(env.address));
// }
//
// template <Revision rev>
// inline Result<uint64_t> balance(
//     StackPointer sp, MachineState const &mstate, SystemState &sstate)
//     noexcept
//{
//     auto const &address = sp.pop();
//     auto const addr = intx::be::trunc<Address>(address);
//
//     uint64_t cost = 0;
//     if (rev >= Revision::Berlin &&
//         sstate.access_account(addr) == AccessStatus::Cold) {
//         if (mstate.gas_left < additional_cold_account_access_cost) {
//             return Status::OutOfGas;
//         }
//         cost = additional_cold_account_access_cost;
//     }
//
//     sp.push(intx::be::load<uint256>(sstate.get_balance(addr)));
//     return cost;
// }
//
// inline void origin(StackPointer sp, ExecutionEnvironment const &env) noexcept
//{
//     sp.push(intx::be::load<uint256>(env.origin));
// }
//
// inline void caller(StackPointer sp, ExecutionEnvironment const &env) noexcept
//{
//     sp.push(intx::be::load<uint256>(env.sender));
// }
//
// inline void callvalue(StackPointer sp, ExecutionEnvironment const &env)
// noexcept
//{
//     sp.push(intx::be::load<uint256>(env.value));
// }

inline Status calldataload(StackPointer sp, ExecutionState const &state)
{
    auto const &i = sp.pop();

    if (i >= state.env.input_data.size()) {
        sp.push(0);
    }
    else {
        MONAD_ASSERT(i <= std::numeric_limits<size_t>::max());
        auto const sv = state.env.input_data.substr(
            static_cast<size_t>(i), sizeof(bytes32_t));
        bytes32_t bytes;
        std::copy_n(sv.data(), sv.size(), bytes.bytes);
        // YP Appendix H: When interpreting 256-bit binary values as integers,
        // the representation is big-endian.
        sp.push(intx::be::load<uint256_t>(bytes));
    }

    return Status::Success;
}

// inline void
// calldatasize(StackPointer sp, ExecutionEnvironment const &env) noexcept
//{
//     sp.push(env.input_data.size());
// }
//
// inline Result<uint64_t> calldatacopy(
//     StackPointer sp, MachineState &mstate,
//     ExecutionEnvironment const &env) noexcept
//{
//     auto const &dest_offset = sp.pop();
//     auto const &offset = sp.pop();
//     auto const &size = sp.pop();
//
//     return copy_impl(mstate, env.input_data, dest_offset, offset, size);
// }
//
// inline void codesize(StackPointer sp, ExecutionEnvironment const &env)
// noexcept
//{
//     sp.push(env.code.size());
// }
//
// inline Result<uint64_t> codecopy(
//     StackPointer sp, MachineState &mstate,
//     ExecutionEnvironment const &env) noexcept
//{
//     auto const &destOffset = sp.pop();
//     auto const &offset = sp.pop();
//     auto const &size = sp.pop();
//
//     return copy_impl(mstate, env.code, dest_offset, offset, size);
// }
//
// inline void gasprice(StackPointer sp, ExecutionEnvironment const &env)
// noexcept
//{
//     sp.push(intx::be::load<uint256>(env.gas_price));
// }
//
// template <Revision rev>
// inline Result<uint64_t> extcodesize(
//     StackPointer sp, MachineState const &mstate, SystemState &sstate)
//     noexcept
//{
//     auto const &address = sp.pop();
//     auto const addr = intx::be::trunc<Address>(address);
//
//     uint64_t cost = 0;
//     if (rev >= EVMC_BERLIN &&
//         sstate.access_account(addr) == AccessStatus::Cold) {
//         if (mstate.gas_left < additional_cold_account_access_cost) {
//             return Status::OutOfGas;
//         }
//         cost = additional_cold_account_access_cost;
//     }
//
//     sp.push(sstate.get_code_size(addr));
//     return cost;
// }
//
// template <Revision rev>
// Result<uint64_t>
// extcodecopy(StackPointer sp, MachineState &mstate, SystemState &sstate)
// noexcept
//{
//     auto const address = intx::be::trunc<evmc::address>(sp.pop());
//     auto const &dest_offset = sp.pop();
//     auto const &offset = sp.pop();
//     auto const &size = sp.pop();
//
//     uint64_t grow_cost = 0;
//     if (size) {
//         BOOST_OUTOME_TRY(
//             grow_cost,
//             mstate.memory.grow_if_needed(mstate.gas_left, dest_offset,
//             size));
//         MONAD_ASSERT(grow_cost <= mstate.gas_left);
//         MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());
//         MONAD_ASSERT(dest_offset <= std::numeric_limits<size_t>::max());
//     }
//
//     auto const size_z = static_cast<size_t>(size);
//     auto const cost = copy_cost(size_z);
//
//     if (mstate.gas_left < (grow_cost + cost)) {
//         return Status::OutOfGas;
//     }
//
//     uint64_t additional_cost = 0;
//     if (rev >= Revision::Berlin &&
//         sstate.access_account(address) == AccessStatus::Cold) {
//         if (gas_left <
//             (grow_cost + cost + additional_cold_account_access_cost)) {
//             return Status::OutOfGas;
//         }
//         additional_cost = additional_cold_account_access_cost;
//     }
//
//     if (size_z) {
//         auto dst = mstate.memory.substr(dest_offset, size);
//         auto const ncopied = sstate.copy_code(
//             address, std::min(Memory::max_size, offset), dst.data(), size);
//         if (ncopied < size) {
//             std::fill_n(dst.data() + ncopied, size - ncopied, 0);
//         }
//     }
//
//     return grow_cost + cost + additional_cost;
// }
//
// inline void
// returndatasize(StackPointer sp, ExecutionState const &state) noexcept
//{
//     sp.push(state.last_return_data.size());
// }
//
// inline Status returndatacopy(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const &dest_offset = stack.pop();
//     auto const &offset = stack.pop();
//     auto const &size = stack.pop();
//
//     if (size == 0) {
//         return Status::Success;
//     }
//
//     BOOST_OUTOME_TRY(
//         auto const grow_cost,
//         mstate.memory.grow_if_needed(mstate.gas_left, dest_offset, size));
//     MONAD_ASSERT(grow_cost <= state.mstate.gas_left);
//     MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());
//     MONAD_ASSERT(dest_offset <= std::numeric_limits<size_t>::max());
//     auto const size_z = static_cast<size_t>(size);
//
//     state.mstate.gas_left -= grow_cost;
//
//     if ((offset + size) > state.last_return_data.size()) {
//         return Status::InvalidMemoryAccess;
//     }
//
//     auto const cost = copy_cost(size_z);
//     if (state.gas_left < cost) {
//         return Status::OutOfGas;
//     }
//     state.mstate.gas_left -= cost;
//
//     if (size_z) {
//         auto dst = state.mstate.memory.substr(
//             static_cast<size_t>(dest_offset), size_z);
//         std::copy_n(state.last_return_data.data(), size_z, dst.data());
//     }
//
//     return Status::Success;
// }
//
// template <Revision rev>
// inline Status extcodehash(StackPointer sp, ExecutionState &state) noexcept
//{
//     auto const &address = stack.pop();
//     auto const addr = intx::be::trunc<evmc::address>(address);
//
//     if (rev >= EVMC_BERLIN &&
//         state.sstate.access_account(addr) == AccessStatus::Cold) {
//         if (state.gas_left < additional_cold_account_access_cost) {
//             return Status::OutOfGas;
//         }
//         state.gas_left -= additional_cold_account_access_cost;
//     }
//
//     sp.push(intx::be::load<uint256>(state.sstate.get_code_hash(addr)));
//     return Status::Success;
// }
//
MONAD_EVM_NAMESPACE_END
