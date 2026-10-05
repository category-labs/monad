// Copyright (C) 2026 Category Labs, Inc.
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
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <concepts>
#include <cstdint>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

enum class Dtype : uint8_t
{
    int8 = 0,
    uint8,
    int16,
    uint16,
    int32,
    uint32,
    int64,
    uint64,
    Last_valid_dtype = uint64,
};

// Size in bytes of one element
[[gnu::always_inline]]
inline uint64_t dtype_size(Dtype const dtype)
{
    switch (dtype) {
    case Dtype::int8:
    case Dtype::uint8:
        return 1;
    case Dtype::int16:
    case Dtype::uint16:
        return 2;
    case Dtype::int32:
    case Dtype::uint32:
        return 4;
    case Dtype::int64:
    case Dtype::uint64:
        return 8;
    }
    MONAD_ABORT();
}

// Calls `f` with the C++ element type for `dtype` as its template argument
template <typename F>
[[gnu::always_inline]]
inline auto visit_dtype(Dtype const dtype, F &&f)
{
    switch (dtype) {
    case Dtype::int8:
        return f.template operator()<int8_t>();
    case Dtype::uint8:
        return f.template operator()<uint8_t>();
    case Dtype::int16:
        return f.template operator()<int16_t>();
    case Dtype::uint16:
        return f.template operator()<uint16_t>();
    case Dtype::int32:
        return f.template operator()<int32_t>();
    case Dtype::uint32:
        return f.template operator()<uint32_t>();
    case Dtype::int64:
        return f.template operator()<int64_t>();
    case Dtype::uint64:
        return f.template operator()<uint64_t>();
    }
    MONAD_ABORT();
}

// The Dtype for a C++ element type; the inverse of visit_dtype
template <typename T>
consteval Dtype dtype_of()
{
    if constexpr (std::same_as<T, int8_t>) {
        return Dtype::int8;
    }
    else if constexpr (std::same_as<T, uint8_t>) {
        return Dtype::uint8;
    }
    else if constexpr (std::same_as<T, int16_t>) {
        return Dtype::int16;
    }
    else if constexpr (std::same_as<T, uint16_t>) {
        return Dtype::uint16;
    }
    else if constexpr (std::same_as<T, int32_t>) {
        return Dtype::int32;
    }
    else if constexpr (std::same_as<T, uint32_t>) {
        return Dtype::uint32;
    }
    else if constexpr (std::same_as<T, int64_t>) {
        return Dtype::int64;
    }
    else if constexpr (std::same_as<T, uint64_t>) {
        return Dtype::uint64;
    }
    else {
        static_assert(false, "no Dtype for this type");
    }
}



MONAD_GRAPH_EVAL_NAMESPACE_END
