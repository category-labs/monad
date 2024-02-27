#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>

MONAD_EVM_NAMESPACE_BEGIN

struct ExecutionState;

[[gnu::always_inline]] inline Status
add(StackPointer sp, ExecutionState const &) noexcept
{
    auto const &a = sp.pop();
    auto const &b = sp.pop();
    sp.push(a + b);
    return Status::Success;
}

MONAD_EVM_NAMESPACE_END
