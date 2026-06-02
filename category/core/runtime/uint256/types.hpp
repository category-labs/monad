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

#include <category/core/config.hpp>

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>

// This header file defines the shared types used by the uint256 implementation
// and its intrinsics.

MONAD_NAMESPACE_BEGIN

template <typename T>
struct result_with_carry
{
    T value;
    bool carry;

    // Only used in unit tests
    friend inline bool operator==(
        result_with_carry const &lhs, result_with_carry const &rhs) noexcept
        requires std::equality_comparable<T>
    {
        return lhs.value == rhs.value && lhs.carry == rhs.carry;
    }
};

template <typename Q, typename R = Q>
struct div_result
{
    Q quot;
    R rem;

    // Only used in unit tests
    friend inline bool
    operator==(div_result const &lhs, div_result const &rhs) noexcept
        requires std::equality_comparable<Q> && std::equality_comparable<R>
    {
        return lhs.quot == rhs.quot && lhs.rem == rhs.rem;
    }
};

template <size_t M>
using words_t = std::array<uint64_t, M>;

MONAD_NAMESPACE_END
