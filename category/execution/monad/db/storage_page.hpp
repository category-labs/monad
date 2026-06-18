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

#include <boost/container/small_vector.hpp>
#include <evmc/evmc.hpp>

#include <bit>
#include <cstdint>
#include <cstring>

MONAD_NAMESPACE_BEGIN

struct storage_page_t
{
    static constexpr size_t SLOT_SIZE = 32;
    static constexpr size_t PAGE_KEY_SHIFT = 7;
    static constexpr size_t SLOTS = 1 << PAGE_KEY_SHIFT;
    static constexpr size_t NUM_PAIRS = SLOTS / 2;
    static constexpr uint8_t SLOT_OFFSET_MASK = (1 << PAGE_KEY_SHIFT) - 1;

    using bitmap_t = unsigned __int128;

    storage_page_t() noexcept = default;

    bool operator==(storage_page_t const &other) const = default;

    bytes32_t operator[](uint8_t const offset) const
    {
        MONAD_ASSERT(offset < SLOTS);
        if (!has_bit_(offset)) {
            return bytes32_t{};
        }
        return values_[dense_index_(offset)];
    }

    // We provide set() rather than a bytes32_t &operator[] for write, because
    // zero slots are not stored in the dense values_, so there's no backing
    // cell to hand out a reference to.
    // A write must also update the bitmap and insert/erase the value
    // accordingly.
    void set(uint8_t const offset, bytes32_t const &value)
    {
        MONAD_ASSERT(offset < SLOTS);
        bool const is_zero = (value == bytes32_t{});
        bool const was_present = has_bit_(offset);
        size_t const dense_idx = dense_index_(offset);
        auto const it =
            values_.begin() + static_cast<std::ptrdiff_t>(dense_idx);
        if (is_zero) {
            if (!was_present) {
                return;
            }
            values_.erase(it);
            clear_bit_(offset);
        }
        else {
            if (was_present) {
                values_[dense_idx] = value;
            }
            else {
                values_.insert(it, value);
                set_bit_(offset);
            }
        }
    }

    bool is_empty() const
    {
        return bitmap_ == 0;
    }

    bitmap_t bitmap() const
    {
        return bitmap_;
    }

    // Number of non-zero slots.
    size_t size() const
    {
        return values_.size();
    }

    // Bit i of the result is set iff at least one of slots 2i, 2i+1 is
    // non-zero. Used by page_commit to walk only the active pair-leaves.
    // Defined in storage_page.cpp to keep the BMI2 (_pext_u64) dependency
    // out of this header and off every translation unit that includes it.
    uint64_t pair_bitmap() const;

private:
    bool has_bit_(uint8_t const i) const
    {
        return (bitmap_ >> i) & static_cast<bitmap_t>(1);
    }

    void set_bit_(uint8_t const i)
    {
        bitmap_ |= static_cast<bitmap_t>(1) << i;
    }

    void clear_bit_(uint8_t const i)
    {
        bitmap_ &= ~(static_cast<bitmap_t>(1) << i);
    }

    // Position in values_ corresponding to slot offset i. Equal to the
    // number of set bits strictly below i in the bitmap.
    size_t dense_index_(uint8_t const i) const
    {
        bitmap_t const below = bitmap_ & ((static_cast<bitmap_t>(1) << i) - 1);
        return static_cast<size_t>(
                   std::popcount(static_cast<uint64_t>(below))) +
               static_cast<size_t>(
                   std::popcount(static_cast<uint64_t>(below >> 64)));
    }

    static constexpr size_t INLINE_VALUES = 4;

    // Bit i set iff slot i has a non-zero value. values_ holds the values
    // in slot-index order; values_[k] is the value for the k-th set bit.
    bitmap_t bitmap_{0};
    boost::container::small_vector<bytes32_t, INLINE_VALUES> values_;
};

inline bytes32_t compute_page_key(bytes32_t const &storage_key)
{
    uint256_t const key_int = load_be<uint256_t>(storage_key.bytes);
    uint256_t const shifted = key_int >> storage_page_t::PAGE_KEY_SHIFT;
    return store_be_as<bytes32_t>(shifted);
}

inline uint8_t compute_slot_offset(bytes32_t const &storage_key)
{
    return storage_key.bytes[31] & storage_page_t::SLOT_OFFSET_MASK;
}

inline bytes32_t
compute_slot_key(bytes32_t const &page_key, uint8_t const slot_offset)
{
    uint256_t const page_int = load_be<uint256_t>(page_key.bytes);
    uint256_t const slot_int =
        (page_int << storage_page_t::PAGE_KEY_SHIFT) | slot_offset;
    return store_be_as<bytes32_t>(slot_int);
}

bytes32_t page_commit(storage_page_t const &page);

// Storage page run-length encoding (RLE)
// TODO: review the implementation, it can be changed without affecting the
// interface.
byte_string encode_storage_page(storage_page_t const &page);
Result<storage_page_t> decode_storage_page(byte_string_view enc);

MONAD_NAMESPACE_END
