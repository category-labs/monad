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

namespace monad::vm
{
    // Mirrors evmc_call_kind 1:1; values asserted equal in message.cpp.
    enum class CallKind : uint32_t
    {
        Call = 0,
        DelegateCall = 1,
        CallCode = 2,
        Create = 3,
        Create2 = 4,
        EofCreate = 5
    };

    // Mirrors evmc_flags 1:1; values asserted equal in message.cpp.
    enum class CallFlags : uint32_t
    {
        Static = 1,
        Delegated = 2
    };

    // Mirrors the category-labs fork's evmc_message field-for-field (no
    // code/code_size, memory-pool fields present); layout asserted in
    // message.cpp.
    struct Message
    {
        CallKind kind;
        uint32_t flags;
        int32_t depth;
        int64_t gas;
        Address recipient;
        Address sender;
        uint8_t const *input_data;
        size_t input_size;
        bytes32_t value;
        bytes32_t create2_salt;
        Address code_address;
        uint8_t *memory_handle;
        uint8_t *memory;
        uint32_t memory_capacity;
    };
}
