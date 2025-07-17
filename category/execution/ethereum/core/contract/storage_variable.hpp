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
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <intx/intx.hpp>

#include <array>
#include <cstring>
#include <optional>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

template <typename T>
    requires std::has_unique_object_representations_v<T>
class StorageVariable
{
public:
    static constexpr size_t N =
        (sizeof(T) + sizeof(bytes32_t) - 1) / sizeof(bytes32_t);
    using Slots = std::array<bytes32_t, N>;

    static Slots to_slots(T const &t)
    {
        Slots slots{}; // zero-pad the tail
        std::memcpy(&slots[0].bytes, &t, sizeof(T));
        return slots;
    }

    static T from_slots(Slots const &slots)
    {
        auto *const base = &slots[0].bytes[0];
        return unaligned_load<T>(base);
    }

private:
    void store_(Slots const &slots)
    {
        for (size_t i = 0; i < N; ++i) {
            state_.set_storage(
                address_, intx::be::store<bytes32_t>(offset_ + i), slots[i]);
        }
    }

    // TODO: Move state and address to method calls
    State &state_;
    Address const &address_;
    uint256_t const offset_;

public:
    StorageVariable(State &state, Address const &address, bytes32_t const &key)
        : state_{state}
        , address_{address}
        , offset_{intx::be::load<uint256_t>(key)}
    {
    }

    StorageVariable(State &state, Address const &address, uint256_t const &key)
        : state_{state}
        , address_{address}
        , offset_{key}
    {
    }

    T load() const noexcept
    {
        Slots slots;
        for (size_t i = 0; i < N; ++i) {
            slots[i] = state_.get_storage(
                address_, intx::be::store<bytes32_t>(offset_ + i));
        }
        return from_slots(slots);
    }

    std::optional<T> load_checked() const noexcept
    {
        Slots slots;
        bool has_data = false;
        for (size_t i = 0; i < N; ++i) {
            slots[i] = state_.get_storage(
                address_, intx::be::store<bytes32_t>(offset_ + i));
            has_data |= (slots[i] != bytes32_t{});
        }
        return has_data ? from_slots(slots) : std::optional<T>{};
    }

    void store(T const &value)
    {
        store_(to_slots(value));
    }

    void clear()
    {
        store_(Slots{}); // zero all blocks
    }
};

MONAD_NAMESPACE_END
