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

#include <category/core/config.hpp>

#include <algorithm>
#include <array>
#include <bit>

MONAD_NAMESPACE_BEGIN

template <typename T>
[[nodiscard]] constexpr T unaligned_load(unsigned char const *const buf)
{
    std::array<unsigned char, sizeof(T)> data;
    std::copy_n(buf, sizeof(T), data.data());
    return std::bit_cast<T>(data);
}

template <typename T>
constexpr void unaligned_store(unsigned char *const buf, T const &value)
{
    auto data = std::bit_cast<std::array<unsigned char, sizeof(T)>>(value);
    std::copy_n(data.data(), sizeof(T), buf);
}

MONAD_NAMESPACE_END
