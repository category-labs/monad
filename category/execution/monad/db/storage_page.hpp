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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>

#include <evmc/evmc.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct storage_page_t
{
    static constexpr size_t SLOTS = 128;
    static constexpr size_t SLOT_SIZE = 32;
    static constexpr size_t PAGE_KEY_SHIFT = 7;
    static constexpr uint8_t SLOT_OFFSET_MASK = (1 << PAGE_KEY_SHIFT) - 1;

    constexpr storage_page_t() noexcept = default;

    constexpr bool operator==(storage_page_t const &other) const = default;

    // Read access. To write, use set() so the bitmap stays consistent
    // with slot contents.
    bytes32_t const &operator[](uint8_t const offset) const
    {
        MONAD_DEBUG_ASSERT(offset < SLOTS);
        return slots_[offset];
    }

    void set(uint8_t const offset, bytes32_t const &value)
    {
        MONAD_DEBUG_ASSERT(offset < SLOTS);
        slots_[offset] = value;
        unsigned __int128 const bit = static_cast<unsigned __int128>(1)
                                      << offset;
        if (value == bytes32_t{}) {
            bitmap_ &= ~bit;
        }
        else {
            bitmap_ |= bit;
        }
    }

    bool is_empty() const
    {
        return bitmap_ == 0;
    }

    // Bit i is set iff slots_[i] != bytes32_t{}. Hot consumers (the
    // BLAKE3 leaf hasher, sparse iteration) read this directly.
    unsigned __int128 bitmap() const
    {
        return bitmap_;
    }

    // Pointer to the contiguous slot bytes. Used by the BLAKE3 leaf
    // hasher to consume 64-byte slot pairs as raw input.
    uint8_t const *slot_bytes() const
    {
        return reinterpret_cast<uint8_t const *>(slots_);
    }

private:
    bytes32_t slots_[SLOTS]{};
    // In-memory accelerator. Not serialized; the on-disk RLE encoding
    // already encodes presence. Maintained by set() and by
    // decode_storage_page during construction.
    unsigned __int128 bitmap_{0};
};

static_assert(
    sizeof(storage_page_t) ==
    storage_page_t::SLOTS * storage_page_t::SLOT_SIZE +
        sizeof(unsigned __int128));

inline bytes32_t compute_page_key(bytes32_t const &storage_key)
{
    uint256_t const key_int = uint256_t::load_be(storage_key.bytes);
    uint256_t const shifted = key_int >> storage_page_t::PAGE_KEY_SHIFT;
    return shifted.store_be<bytes32_t>();
}

inline uint8_t compute_slot_offset(bytes32_t const &storage_key)
{
    return storage_key.bytes[31] & storage_page_t::SLOT_OFFSET_MASK;
}

inline bytes32_t
compute_slot_key(bytes32_t const &page_key, uint8_t slot_offset)
{
    uint256_t const page_int = uint256_t::load_be(page_key.bytes);
    uint256_t const slot_int =
        (page_int << storage_page_t::PAGE_KEY_SHIFT) | slot_offset;
    return slot_int.store_be<bytes32_t>();
}

bytes32_t page_commit(storage_page_t const &page);

// Storage page run-length encoding (RLE)
// TODO: review the implementation, it can be changed without affecting the
// interface.
byte_string encode_storage_page(storage_page_t const &page);
Result<storage_page_t> decode_storage_page(byte_string_view enc);

MONAD_NAMESPACE_END
