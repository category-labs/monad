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

#include <evmc/evmc.h>

#ifdef __cplusplus
extern "C"
{
#endif

// Mirrors evmc_status_code 1:1; values asserted equal in status_code.cpp, so
// every wire and ABI encoding of a status is unchanged. Coarser VM exit codes
// live in vm::runtime::StatusCode.
//
// The <evmc/evmc.h> include serves only the conversions below; both go with
// EXE-173. Do not include this from the evmc-free C ABI headers.
enum monad_status_code
{
    MONAD_STATUS_SUCCESS = 0,
    MONAD_STATUS_FAILURE = 1,
    MONAD_STATUS_REVERT = 2,
    MONAD_STATUS_OUT_OF_GAS = 3,
    MONAD_STATUS_INVALID_INSTRUCTION = 4,
    MONAD_STATUS_UNDEFINED_INSTRUCTION = 5,
    MONAD_STATUS_STACK_OVERFLOW = 6,
    MONAD_STATUS_STACK_UNDERFLOW = 7,
    MONAD_STATUS_BAD_JUMP_DESTINATION = 8,
    MONAD_STATUS_INVALID_MEMORY_ACCESS = 9,
    MONAD_STATUS_CALL_DEPTH_EXCEEDED = 10,
    MONAD_STATUS_STATIC_MODE_VIOLATION = 11,
    MONAD_STATUS_PRECOMPILE_FAILURE = 12,
    MONAD_STATUS_CONTRACT_VALIDATION_FAILURE = 13,
    MONAD_STATUS_ARGUMENT_OUT_OF_RANGE = 14,
    MONAD_STATUS_WASM_UNREACHABLE_INSTRUCTION = 15,
    MONAD_STATUS_WASM_TRAP = 16,
    MONAD_STATUS_INSUFFICIENT_BALANCE = 17,
    // Fork-only: no upstream evmc counterpart.
    MONAD_STATUS_RESERVE_BALANCE_VIOLATION = 18,

    MONAD_STATUS_INTERNAL_ERROR = -1,
    MONAD_STATUS_REJECTED = -2,
    MONAD_STATUS_OUT_OF_MEMORY = -3
};

char const *monad_status_code_to_string(enum monad_status_code code);

enum evmc_status_code to_evmc_status_code(enum monad_status_code code);
enum monad_status_code from_evmc_status_code(enum evmc_status_code code);

#ifdef __cplusplus
} // extern "C"
#endif
