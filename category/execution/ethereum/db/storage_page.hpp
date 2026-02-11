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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>

#include <evmc/evmc.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <bit>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

struct storage_page_t
{
    static constexpr size_t SLOTS = 32;
    static constexpr size_t SLOT_SIZE = 32;
    static constexpr size_t SLOT_BITS = std::bit_width(SLOTS) - 1;
    static constexpr uint8_t SLOT_MASK = SLOTS - 1;

    bytes32_t slots[SLOTS];

    constexpr storage_page_t() noexcept
        : slots{}
    {
    }

    constexpr bool operator==(storage_page_t const &other) const = default;

    bytes32_t &operator[](uint8_t const offset)
    {
        return slots[offset];
    }

    bytes32_t const &operator[](uint8_t const offset) const
    {
        return slots[offset];
    }

    bool is_empty() const
    {
        return std::all_of(
            std::begin(slots), std::end(slots), [](bytes32_t const &s) {
                return s == bytes32_t{};
            });
    }
};

static_assert(
    sizeof(storage_page_t) ==
    storage_page_t::SLOTS * storage_page_t::SLOT_SIZE);
static_assert(alignof(storage_page_t) == 1);

inline bytes32_t compute_page_key(bytes32_t const &storage_key)
{
    uint256_t const key_int = intx::be::load<uint256_t>(storage_key);
    uint256_t const shifted = key_int >> storage_page_t::SLOT_BITS;
    return intx::be::store<bytes32_t>(shifted);
}

inline uint8_t compute_slot_offset(bytes32_t const &storage_key)
{
    return storage_key.bytes[31] & storage_page_t::SLOT_MASK;
}

inline bytes32_t
compute_slot_key(bytes32_t const &page_key, uint8_t slot_offset)
{
    uint256_t const page_int = intx::be::load<uint256_t>(page_key);
    uint256_t const slot_int =
        (page_int << storage_page_t::SLOT_BITS) | slot_offset;
    return intx::be::store<bytes32_t>(slot_int);
}

// RLE-encode/decode storage page slot values.
// Optimizes for minimum encoding size (both empty and non-empty slots) and
// fast encoding speed. See storage_page.cpp for format details.
byte_string encode_storage_page(storage_page_t const &);

Result<storage_page_t> decode_storage_page(byte_string_view &);

MONAD_NAMESPACE_END
