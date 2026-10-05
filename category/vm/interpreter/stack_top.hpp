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

#include <category/core/runtime/uint256.hpp>

#include <cstddef>
#include <type_traits>

namespace monad::vm::interpreter
{
    // A typed wrapper around the interpreter's top-element pointer.
    // Callers must check stack requirements before accessing values.
    class StackTop
    {
        uint256_t *ptr_;

    public:
        explicit constexpr StackTop(uint256_t *const ptr)
            : ptr_{ptr}
        {
        }

        constexpr uint256_t &operator*() const
        {
            return (*this)[0];
        }

        constexpr uint256_t *operator->() const
        {
            return &(*this)[0];
        }

        // Index 0 is the top value, -1 is the value below it, and so on.
        constexpr uint256_t &operator[](std::ptrdiff_t const index) const
        {
            return *(ptr_ + index);
        }

        // Only writable when the stack is not full. Does not advance the top.
        constexpr uint256_t *next_slot() const
        {
            return ptr_ + 1;
        }

        constexpr StackTop &operator+=(std::ptrdiff_t const delta)
        {
            ptr_ += delta;
            return *this;
        }

        constexpr StackTop operator+(std::ptrdiff_t const delta) const
        {
            auto result = *this;
            result += delta;
            return result;
        }

        constexpr StackTop &operator--()
        {
            --ptr_;
            return *this;
        }

        constexpr StackTop operator--(int)
        {
            auto result = *this;
            --*this;
            return result;
        }
    };

    // Instruction dispatch passes this by value through musttail calls.
    static_assert(sizeof(StackTop) == sizeof(uint256_t *));
    static_assert(std::is_trivially_copyable_v<StackTop>);
}
