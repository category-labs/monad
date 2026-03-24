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

#include <category/core/detail/start_lifetime_as_polyfill.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <compare>
#include <cstring>
#include <span>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

template <typename T>
[[nodiscard, gnu::always_inline]] constexpr T
unaligned_load(unsigned char const *const buf)
{
    std::array<unsigned char, sizeof(T)> data;
    std::copy_n(buf, sizeof(T), data.data());
    return std::bit_cast<T>(data);
}

template <typename T>
[[gnu::always_inline]] constexpr void
unaligned_store(unsigned char *const buf, T const &value)
{
    auto data = std::bit_cast<std::array<unsigned char, sizeof(T)>>(value);
    std::copy_n(data.data(), sizeof(T), buf);
}

// Element type for std::span over a packed unaligned array of T.
//
// Stores T as raw bytes; read via std::bit_cast, write via memcpy, so the
// compiler emits unaligned load/store instructions and no alignment fault can
// occur.  Works for any trivially-copyable T including non-POD class types.
//
// Implicit conversion to/from T means it behaves transparently at most call
// sites. Use as_unaligned_span() to construct a std::span<unaligned_t<T>>.
//
// Note: std::min(T, unaligned_t<T>) fails template deduction (mixed-type case
// only; std::min(unaligned_t<T>, unaligned_t<T>) deduces fine); use
// std::min<T>(...) or a range-for loop with a T loop variable.
//
// [[gnu::may_alias]] — an unaligned_t<T>* may alias arbitrary storage,
//                      mirroring the permission that unsigned char* already
//                      has in the other direction.  Prevents the compiler from
//                      assuming the typed pointer is disjoint from the
//                      surrounding heterogeneous Node layout.
template <typename T>
struct [[gnu::may_alias]] unaligned_t
{
    static_assert(std::is_trivially_copyable_v<T>);

    unsigned char bytes[sizeof(T)];

    // NOLINTNEXTLINE(google-explicit-constructor)
    operator T() const noexcept
    {
        return std::bit_cast<T>(bytes);
    }

    // implicit write
    unaligned_t &operator=(T const &v) noexcept
    {
        std::memcpy(bytes, &v, sizeof(v));
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

// Returns std::span<unaligned_t<T>> over [ptr, ptr + n*sizeof(T)).
// Safe because [[gnu::may_alias]] permits unaligned_t<T>* to alias the buffer.
template <typename T>
[[nodiscard]] std::span<unaligned_t<T>>
as_unaligned_span(unsigned char *ptr, unsigned n) noexcept
{
    return {monad::start_lifetime_as_array<unaligned_t<T>>(ptr, n), n};
}

// Const overload.
template <typename T>
[[nodiscard]] std::span<unaligned_t<T> const>
as_unaligned_span(unsigned char const *ptr, unsigned n) noexcept
{
    return {monad::start_lifetime_as_array<unaligned_t<T>>(ptr, n), n};
}

MONAD_NAMESPACE_END
