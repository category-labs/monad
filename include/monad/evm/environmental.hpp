#pragma once

#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>

MONAD_EVM_NAMESPACE_BEGIN

inline Status address(StackPointer sp, ExecutionState const &state)
{
    sp.push(intx::be::load<uint256_t>(state.env.address));
    return Status::Success;
}

inline Status origin(StackPointer sp, ExecutionState const &state)
{
    sp.push(intx::be::load<uint256_t>(state.env.origin));
    return Status::Success;
}

inline Status caller(StackPointer sp, ExecutionState const &state)
{
    sp.push(intx::be::load<uint256_t>(state.env.sender));
    return Status::Success;
}

inline Status callvalue(StackPointer sp, ExecutionState const &state)
{
    sp.push(intx::be::load<uint256_t>(to_bytes(state.env.value)));
    return Status::Success;
}

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

inline Status calldatasize(StackPointer sp, ExecutionState const &state)
{
    sp.push(state.env.input_data.size());
    return Status::Success;
}

inline Status codesize(StackPointer sp, ExecutionState const &state)
{
    sp.push(state.env.code.size());
    return Status::Success;
}

inline Status gasprice(StackPointer sp, ExecutionState const &state)
{
    sp.push(intx::be::load<uint256_t>(to_bytes(state.env.gas_price)));
    return Status::Success;
}

MONAD_EVM_NAMESPACE_END
