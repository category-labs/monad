#pragma once

#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>

MONAD_EVM_NAMESPACE_BEGIN

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

MONAD_EVM_NAMESPACE_END
