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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>

#include <cstddef>
#include <cstdint>

// Mirrors evmc_call_kind 1:1; values asserted equal in message.cpp.
enum monad_call_kind
{
    MONAD_CALL = 0,
    MONAD_DELEGATECALL = 1,
    MONAD_CALLCODE = 2,
    MONAD_CREATE = 3,
    MONAD_CREATE2 = 4,
    MONAD_EOFCREATE = 5
};

// Mirrors evmc_flags 1:1; values asserted equal in message.cpp.
enum monad_call_flags
{
    MONAD_STATIC = 1,
    MONAD_DELEGATED = 2
};

// Mirrors the category-labs fork's evmc_message field-for-field (no
// code/code_size, memory-pool fields present); layout asserted in message.cpp.
struct monad_message
{
    monad_call_kind kind;
    uint32_t flags;
    int32_t depth;
    int64_t gas;
    monad::Address recipient;
    monad::Address sender;
    uint8_t const *input_data;
    size_t input_size;
    monad::bytes32_t value;
    monad::bytes32_t create2_salt;
    monad::Address code_address;
    uint8_t *memory_handle;
    uint8_t *memory;
    uint32_t memory_capacity;
};

struct evmc_message;

// Bridges for the evmc::HostInterface::call vtable slot and the evmone ABI;
// go with EXE-173.
evmc_message to_evmc_message(monad_message const &);
monad_message from_evmc_message(evmc_message const &);
