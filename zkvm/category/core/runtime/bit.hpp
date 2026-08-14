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

#include <bit>
#include <concepts>
#include <cstdint>

namespace monad::bit
{
    template <std::integral T>
    [[nodiscard, gnu::always_inline]] inline constexpr T
    byteswap(T const x) noexcept
    {
        if constexpr (sizeof(T) == 8) {
            auto v = static_cast<uint64_t>(x);
            v = ((v & 0x00FF00FF00FF00FFull) << 8) |
                ((v >> 8) & 0x00FF00FF00FF00FFull);
            v = ((v & 0x0000FFFF0000FFFFull) << 16) |
                ((v >> 16) & 0x0000FFFF0000FFFFull);
            return static_cast<T>((v << 32) | (v >> 32));
        }
        else if constexpr (sizeof(T) == 4) {
            auto v = static_cast<uint32_t>(x);
            v = ((v & 0x00FF00FFu) << 8) | ((v >> 8) & 0x00FF00FFu);
            return static_cast<T>((v << 16) | (v >> 16));
        }
        else {
            return std::byteswap(x);
        }
    }
}
