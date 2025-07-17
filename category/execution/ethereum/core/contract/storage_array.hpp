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

#include <category/execution/ethereum/core/contract/storage_variable.hpp>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

// An array in the State trie. First index is the size.
template <typename T>
    requires std::has_unique_object_representations_v<T>
class StorageArray
{
    // TODO: Move state and address to method calls
    State &state_;
    Address const &address_;
    StorageVariable<u64_be> length_;
    uint256_t const start_index_;

    static constexpr size_t SLOT_PER_ELEM = StorageVariable<T>::N;

public:
    StorageArray(State &state, Address const &address, bytes32_t const &slot)
        : state_{state}
        , address_{address}
        , length_{StorageVariable<u64_be>(state, address, slot)}
        , start_index_{intx::be::load<uint256_t>(slot) + 1}
    {
    }

    uint64_t length() const noexcept
    {
        return length_.load().native();
    }

    bool empty() const noexcept
    {
        return length() == 0;
    }

    StorageVariable<T> get(uint64_t const index) const noexcept
    {
        uint256_t const offset = start_index_ + index * SLOT_PER_ELEM;
        return StorageVariable<T>{
            state_, address_, intx::be::store<bytes32_t>(offset)};
    }

    void push(T const &value) noexcept
    {
        auto const len = length();
        uint256_t const offset = start_index_ + len * SLOT_PER_ELEM;
        StorageVariable<T> var{
            state_, address_, intx::be::store<bytes32_t>(offset)};
        var.store(value);
        length_.store(len + 1);
    }

    T pop() noexcept
    {
        uint64_t len = length();
        MONAD_ASSERT(len > 0);
        len = len - 1;
        auto var = get(len);
        T const value = var.load();
        var.clear();
        length_.store(len);
        return value;
    }
};

MONAD_NAMESPACE_END
