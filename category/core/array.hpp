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

#include <array>
#include <cstddef>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    template <class T, size_t... Is, class... Args>
    constexpr std::array<T, sizeof...(Is)>
    make_array_impl(std::index_sequence<Is...>, Args &&...args)
    {
        return {{((void)Is, T{std::forward<Args>(args)...})...}};
    }
}
/*! \brief Return a `std::array<T, N>` with each item constructed
from `args...`. Supports immovable types.
*/
template <class T, size_t N, class... Args>
    requires(std::is_constructible_v<T, Args...>)
constexpr std::array<T, N>
make_array(std::piecewise_construct_t, Args &&...args)
{
    return detail::make_array_impl<T>(
        std::make_index_sequence<N>(), std::forward<Args>(args)...);
}

MONAD_NAMESPACE_END
