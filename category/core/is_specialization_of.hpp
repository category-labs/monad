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

// https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2020/p2098r0.pdf

#pragma once

#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

template <template <auto...> class Template, typename T>
struct is_specialization_of : std::false_type
{
};

template <template <auto...> class Template, auto... Args>
struct is_specialization_of<Template, Template<Args...>> : std::true_type
{
};

template <template <auto...> class Template, typename T>
inline constexpr bool is_specialization_of_v =
    is_specialization_of<Template, T>::value;

MONAD_NAMESPACE_END
