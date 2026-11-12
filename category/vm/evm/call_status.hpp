// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

enum class CallStatus : int
{
    Success = 0,
    Failure = 1,
    Revert = 2,
    OutOfGas = 3,
    InvalidInstruction = 4,
    UndefinedInstruction = 5,
    StackOverflow = 6,
    StackUnderflow = 7,
    BadJumpDestination = 8,
    InvalidMemoryAccess = 9,
    CallDepthExceeded = 10,
    StaticModeViolation = 11,
    PrecompileFailure = 12,
    ContractValidationFailure = 13,
    ArgumentOutOfRange = 14,
    InsufficientBalance = 17,
    ReserveBalanceViolation = 18,

    InternalError = -1,
    Rejected = -2,
    OutOfMemory = -3
};

MONAD_NAMESPACE_END
