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
#include <category/core/int.hpp>

MONAD_NAMESPACE_BEGIN

inline constexpr uint256_t WEI{1};
inline constexpr uint256_t GWEI{1'000'000'000};
inline constexpr uint256_t ETHER{1'000'000'000'000'000'000};

namespace literals
{
    consteval uint256_t operator""_wei(unsigned long long const x) noexcept
    {
        return uint256_t{x};
    }

    consteval uint256_t operator""_gwei(unsigned long long const x) noexcept
    {
        return uint256_t{x} * GWEI;
    }

    consteval uint256_t operator""_ether(unsigned long long const x) noexcept
    {
        return uint256_t{x} * ETHER;
    }
}

using literals::operator""_wei;
using literals::operator""_gwei;
using literals::operator""_ether;

MONAD_NAMESPACE_END
