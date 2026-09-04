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

#include <category/core/assert.h>
#include <category/vm/evm/status_code.h>

#include <evmc/evmc.h>

#include <utility>

// Value-equality with evmc_status_code; the conversions below rely on it.
#define MONAD_ASSERT_STATUS_EQ(name)                                           \
    static_assert(                                                             \
        std::to_underlying(MONAD_STATUS_##name) ==                             \
        std::to_underlying(EVMC_##name))

MONAD_ASSERT_STATUS_EQ(SUCCESS);
MONAD_ASSERT_STATUS_EQ(FAILURE);
MONAD_ASSERT_STATUS_EQ(REVERT);
MONAD_ASSERT_STATUS_EQ(OUT_OF_GAS);
MONAD_ASSERT_STATUS_EQ(INVALID_INSTRUCTION);
MONAD_ASSERT_STATUS_EQ(UNDEFINED_INSTRUCTION);
MONAD_ASSERT_STATUS_EQ(STACK_OVERFLOW);
MONAD_ASSERT_STATUS_EQ(STACK_UNDERFLOW);
MONAD_ASSERT_STATUS_EQ(BAD_JUMP_DESTINATION);
MONAD_ASSERT_STATUS_EQ(INVALID_MEMORY_ACCESS);
MONAD_ASSERT_STATUS_EQ(CALL_DEPTH_EXCEEDED);
MONAD_ASSERT_STATUS_EQ(STATIC_MODE_VIOLATION);
MONAD_ASSERT_STATUS_EQ(PRECOMPILE_FAILURE);
MONAD_ASSERT_STATUS_EQ(CONTRACT_VALIDATION_FAILURE);
MONAD_ASSERT_STATUS_EQ(ARGUMENT_OUT_OF_RANGE);
MONAD_ASSERT_STATUS_EQ(WASM_UNREACHABLE_INSTRUCTION);
MONAD_ASSERT_STATUS_EQ(WASM_TRAP);
MONAD_ASSERT_STATUS_EQ(INSUFFICIENT_BALANCE);
MONAD_ASSERT_STATUS_EQ(INTERNAL_ERROR);
MONAD_ASSERT_STATUS_EQ(REJECTED);
MONAD_ASSERT_STATUS_EQ(OUT_OF_MEMORY);

#undef MONAD_ASSERT_STATUS_EQ

// Fork-only, and evmc's spelling carries a vendor prefix the macro can't reach.
static_assert(
    std::to_underlying(MONAD_STATUS_RESERVE_BALANCE_VIOLATION) ==
    std::to_underlying(EVMC_MONAD_RESERVE_BALANCE_VIOLATION));

// Safe while every code has an evmc counterpart. If you add a Monad-only one,
// give this a range guard: -Wswitch on to_string below is the only trip-wire.
evmc_status_code to_evmc_status_code(monad_status_code const code)
{
    return static_cast<evmc_status_code>(std::to_underlying(code));
}

// Switched, not cast: -Wswitch fails the build if evmc gains a code.
monad_status_code from_evmc_status_code(evmc_status_code const code)
{
    switch (code) {
    case EVMC_SUCCESS:
        return MONAD_STATUS_SUCCESS;
    case EVMC_FAILURE:
        return MONAD_STATUS_FAILURE;
    case EVMC_REVERT:
        return MONAD_STATUS_REVERT;
    case EVMC_OUT_OF_GAS:
        return MONAD_STATUS_OUT_OF_GAS;
    case EVMC_INVALID_INSTRUCTION:
        return MONAD_STATUS_INVALID_INSTRUCTION;
    case EVMC_UNDEFINED_INSTRUCTION:
        return MONAD_STATUS_UNDEFINED_INSTRUCTION;
    case EVMC_STACK_OVERFLOW:
        return MONAD_STATUS_STACK_OVERFLOW;
    case EVMC_STACK_UNDERFLOW:
        return MONAD_STATUS_STACK_UNDERFLOW;
    case EVMC_BAD_JUMP_DESTINATION:
        return MONAD_STATUS_BAD_JUMP_DESTINATION;
    case EVMC_INVALID_MEMORY_ACCESS:
        return MONAD_STATUS_INVALID_MEMORY_ACCESS;
    case EVMC_CALL_DEPTH_EXCEEDED:
        return MONAD_STATUS_CALL_DEPTH_EXCEEDED;
    case EVMC_STATIC_MODE_VIOLATION:
        return MONAD_STATUS_STATIC_MODE_VIOLATION;
    case EVMC_PRECOMPILE_FAILURE:
        return MONAD_STATUS_PRECOMPILE_FAILURE;
    case EVMC_CONTRACT_VALIDATION_FAILURE:
        return MONAD_STATUS_CONTRACT_VALIDATION_FAILURE;
    case EVMC_ARGUMENT_OUT_OF_RANGE:
        return MONAD_STATUS_ARGUMENT_OUT_OF_RANGE;
    case EVMC_WASM_UNREACHABLE_INSTRUCTION:
        return MONAD_STATUS_WASM_UNREACHABLE_INSTRUCTION;
    case EVMC_WASM_TRAP:
        return MONAD_STATUS_WASM_TRAP;
    case EVMC_INSUFFICIENT_BALANCE:
        return MONAD_STATUS_INSUFFICIENT_BALANCE;
    case EVMC_MONAD_RESERVE_BALANCE_VIOLATION:
        return MONAD_STATUS_RESERVE_BALANCE_VIOLATION;
    case EVMC_INTERNAL_ERROR:
        return MONAD_STATUS_INTERNAL_ERROR;
    case EVMC_REJECTED:
        return MONAD_STATUS_REJECTED;
    case EVMC_OUT_OF_MEMORY:
        return MONAD_STATUS_OUT_OF_MEMORY;
    }
    MONAD_ABORT("unhandled evmc_status_code");
}

char const *monad_status_code_to_string(monad_status_code const code)
{
    switch (code) {
    case MONAD_STATUS_SUCCESS:
        return "MONAD_STATUS_SUCCESS";
    case MONAD_STATUS_FAILURE:
        return "MONAD_STATUS_FAILURE";
    case MONAD_STATUS_REVERT:
        return "MONAD_STATUS_REVERT";
    case MONAD_STATUS_OUT_OF_GAS:
        return "MONAD_STATUS_OUT_OF_GAS";
    case MONAD_STATUS_INVALID_INSTRUCTION:
        return "MONAD_STATUS_INVALID_INSTRUCTION";
    case MONAD_STATUS_UNDEFINED_INSTRUCTION:
        return "MONAD_STATUS_UNDEFINED_INSTRUCTION";
    case MONAD_STATUS_STACK_OVERFLOW:
        return "MONAD_STATUS_STACK_OVERFLOW";
    case MONAD_STATUS_STACK_UNDERFLOW:
        return "MONAD_STATUS_STACK_UNDERFLOW";
    case MONAD_STATUS_BAD_JUMP_DESTINATION:
        return "MONAD_STATUS_BAD_JUMP_DESTINATION";
    case MONAD_STATUS_INVALID_MEMORY_ACCESS:
        return "MONAD_STATUS_INVALID_MEMORY_ACCESS";
    case MONAD_STATUS_CALL_DEPTH_EXCEEDED:
        return "MONAD_STATUS_CALL_DEPTH_EXCEEDED";
    case MONAD_STATUS_STATIC_MODE_VIOLATION:
        return "MONAD_STATUS_STATIC_MODE_VIOLATION";
    case MONAD_STATUS_PRECOMPILE_FAILURE:
        return "MONAD_STATUS_PRECOMPILE_FAILURE";
    case MONAD_STATUS_CONTRACT_VALIDATION_FAILURE:
        return "MONAD_STATUS_CONTRACT_VALIDATION_FAILURE";
    case MONAD_STATUS_ARGUMENT_OUT_OF_RANGE:
        return "MONAD_STATUS_ARGUMENT_OUT_OF_RANGE";
    case MONAD_STATUS_WASM_UNREACHABLE_INSTRUCTION:
        return "MONAD_STATUS_WASM_UNREACHABLE_INSTRUCTION";
    case MONAD_STATUS_WASM_TRAP:
        return "MONAD_STATUS_WASM_TRAP";
    case MONAD_STATUS_INSUFFICIENT_BALANCE:
        return "MONAD_STATUS_INSUFFICIENT_BALANCE";
    case MONAD_STATUS_RESERVE_BALANCE_VIOLATION:
        return "MONAD_STATUS_RESERVE_BALANCE_VIOLATION";
    case MONAD_STATUS_INTERNAL_ERROR:
        return "MONAD_STATUS_INTERNAL_ERROR";
    case MONAD_STATUS_REJECTED:
        return "MONAD_STATUS_REJECTED";
    case MONAD_STATUS_OUT_OF_MEMORY:
        return "MONAD_STATUS_OUT_OF_MEMORY";
    }
    MONAD_ABORT("unhandled monad_status_code");
}
