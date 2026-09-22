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
#include <compare>
#include <cstddef>
#include <cstring>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

struct ByteTraits
{
    using char_type = unsigned char;
    using int_type = int;
    using off_type = std::char_traits<char>::off_type;
    using pos_type = std::char_traits<char>::pos_type;
    using state_type = std::char_traits<char>::state_type;
    using comparison_category = std::strong_ordering;

    static constexpr void assign(char_type &c1, char_type const &c2) noexcept
    {
        c1 = c2;
    }

    static constexpr bool eq(char_type const c1, char_type const c2) noexcept
    {
        return c1 == c2;
    }

    static constexpr bool lt(char_type const c1, char_type const c2) noexcept
    {
        return c1 < c2;
    }

    static constexpr int compare(
        char_type const *const s1, char_type const *const s2, size_t const n)
    {
        for (size_t i = 0; i < n; ++i) {
            if (s1[i] != s2[i]) {
                return s1[i] < s2[i] ? -1 : 1;
            }
        }
        return 0;
    }

    static constexpr size_t length(char_type const *const s)
    {
        size_t n = 0;
        while (s[n] != 0) {
            ++n;
        }
        return n;
    }

    static constexpr char_type const *
    find(char_type const *const s, size_t const n, char_type const &c)
    {
        auto const *const end = s + n;
        auto const *const it = std::find(s, end, c);
        return it == end ? nullptr : it;
    }

    static constexpr char_type *
    move(char_type *const s1, char_type const *const s2, size_t const n)
    {
        if consteval {
            auto *const tmp = new char_type[n];
            std::copy(s2, s2 + n, tmp);
            std::copy(tmp, tmp + n, s1);
            delete[] tmp;
            return s1;
        }
        if (n != 0) {
            std::memmove(s1, s2, n);
        }
        return s1;
    }

    static constexpr char_type *
    copy(char_type *const s1, char_type const *const s2, size_t const n)
    {
        std::copy(s2, s2 + n, s1);
        return s1;
    }

    static constexpr char_type *
    assign(char_type *const s, size_t const n, char_type const c)
    {
        std::fill_n(s, n, c);
        return s;
    }

    static constexpr int_type not_eof(int_type const c) noexcept
    {
        return c == eof() ? 0 : c;
    }

    static constexpr char_type to_char_type(int_type const c) noexcept
    {
        return static_cast<char_type>(c);
    }

    static constexpr int_type to_int_type(char_type const c) noexcept
    {
        return c;
    }

    static constexpr bool
    eq_int_type(int_type const c1, int_type const c2) noexcept
    {
        return c1 == c2;
    }

    static constexpr int_type eof() noexcept
    {
        return -1;
    }
};

using byte_string = std::basic_string<unsigned char, ByteTraits>;

template <size_t N>
using byte_string_fixed = std::array<unsigned char, N>;

using byte_string_view = std::basic_string_view<unsigned char, ByteTraits>;

template <size_t N>
constexpr byte_string_view to_byte_string_view(unsigned char const (&a)[N])
{
    return {&a[0], N};
}

template <class T, size_t N>
constexpr byte_string_view to_byte_string_view(std::array<T, N> const &a)
{
    return {a.data(), N};
}

inline byte_string_view to_byte_string_view(std::string const &s)
{
    return {reinterpret_cast<unsigned char const *>(&s[0]), s.size()};
}

MONAD_NAMESPACE_END
