#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/stack_pointer.hpp>

MONAD_EVM_NAMESPACE_BEGIN

inline void blockhash(StackPointer sp, ExecutionState &state) noexcept
{
    auto const &number = sp.pop();
    MONAD_ASSERT(number <= std::numeric_limits<size_t>::max());

    auto const upper_bound = state.env.header.block_number;
    auto const lower_bound = upper_bound > 256 ? upper_bound - 256 : 0;
    auto const hash =
        (number < upper_bound && number >= lower_bound)
            ? state.sstate.get_block_hash(static_cast<size_t>(number))
            : evmc::bytes32{};
    sp.push(intx::be::load<uint256>(hash));
}

inline void coinbase(StackPointer sp, ExecutionState const &state) noexcept
{
    sp.push(intx::be::load<uint256>(state.env.header.beneficiary));
}

inline void timestamp(StackPointer sp, ExecutionState const &state) noexcept
{
    sp.push(state.env.header.timestamp);
}

inline void number(StackPointer sp, ExecutionState const &state) noexcept
{
    sp.push(state.env.header.number);
}

inline void prevrandao(StackPointer sp, ExecutionState const &state) noexcept
{
    sp.push(intx::be::load<uint256>(state.env.header.prev_randao));
}

inline void gaslimit(StackPointer sp, ExecutionState const &state) noexcept
{
    sp.push(state.env.header.gas_limit);
}

inline void chainid(StackPointer sp, ExecutionState const &state) noexcept
{
    // TODO
    sp.push(1);
}

inline void selfbalance(StackPointer sp, ExecutionState &state) noexcept
{
    sp.push(
        intx::be::load<uint256>(state.sstate.get_balance(state.env.address)));
}

inline void basefee(StackPointer sp, ExecutionState &state) noexcept
{
    sp.push(intx::be::load<uint256>(
        to_big_endian(state.env.header.base_fee_per_gas.value_or(0))));
}

MONAD_EVM_NAMESPACE_END
