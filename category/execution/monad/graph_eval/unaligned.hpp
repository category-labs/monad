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

#include "category/execution/monad/graph_eval/config.hpp"
#include <cstdint>
#include <cstring>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

template <typename T>
concept Unaligned = alignof(T) == 1;

template <typename T>
struct [[gnu::may_alias]] unaligned_t
{
    static_assert(std::is_trivially_copyable_v<T>);

    unsigned char bytes[sizeof(T)];

    [[gnu::always_inline]]
    // NOLINTNEXTLINE(google-explicit-constructor)
    inline operator T() const noexcept
    {
        T result;
        __builtin_memcpy(&result, bytes, sizeof(result));
        return result;
    }

    // implicit write
    [[gnu::always_inline]]
    unaligned_t &operator=(T const &v) noexcept
    {
        __builtin_memcpy(bytes, &v, sizeof(v));
        return *this;
    }

    // comparisons (for std::min(unaligned_t, unaligned_t) and range algos)
    bool operator==(unaligned_t const &o) const noexcept
    {
        return static_cast<T>(*this) == static_cast<T>(o);
    }

    auto operator<=>(unaligned_t const &o) const noexcept
    {
        return static_cast<T>(*this) <=> static_cast<T>(o);
    }
};

static_assert(sizeof(unaligned_t<int64_t>) == sizeof(int64_t));
static_assert(alignof(unaligned_t<int64_t>) == 1);

template <typename T>
[[gnu::always_inline]] inline unaligned_t<T> const *
as_elements(uint8_t const *const data)
{
    return reinterpret_cast<unaligned_t<T> const *>(data);
}

template <typename T>
[[gnu::always_inline]] inline unaligned_t<T> *as_elements(uint8_t *const data)
{
    return reinterpret_cast<unaligned_t<T> *>(data);
}
MONAD_GRAPH_EVAL_NAMESPACE_END
