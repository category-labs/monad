// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <intx/intx.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Page key = storage_key >> 7
// Groups storage keys into pages of 128 slots
inline bytes32_t compute_page_key(bytes32_t const &storage_key)
{
    uint256_t const key_int = intx::be::load<uint256_t>(storage_key);
    uint256_t const shifted = key_int >> 7;
    return intx::be::store<bytes32_t>(shifted);
}

// Slot offset = storage_key & 0x7F (lowest 7 bits)
// Returns index within the page (0-127)
inline uint8_t compute_slot_offset(bytes32_t const &storage_key)
{
    return storage_key.bytes[31] & 0x7F;
}

MONAD_NAMESPACE_END
