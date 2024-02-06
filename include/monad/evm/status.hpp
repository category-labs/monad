#pragma once

#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

enum class Status
{
    Success = 0,
    OutOfGas,
    InvalidMemoryAccess,
    StaticModeViolation,
    BadJumpDest,
    Revert,
    UndefinedInstruction,
    StackOverflow,
    StackUnderflow,
    PrecompileFailure,
    InsufficientBalance,
};

MONAD_EVM_NAMESPACE_END
