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

#include <category/core/byte_string.hpp>

#include <cstdint>
#include <stdexcept>

MONAD_NAMESPACE_BEGIN

inline constexpr unsigned char from_hex_digit(char const h)
{
    if (h >= '0' && h <= '9') {
        return static_cast<unsigned char>(h - '0');
    }
    else if (h >= 'a' && h <= 'f') {
        return static_cast<unsigned char>(h - 'a' + 10);
    }
    else if (h >= 'A' && h <= 'F') {
        return static_cast<unsigned char>(h - 'A' + 10);
    }
    else {
        return 0xff;
    }
}

inline constexpr byte_string from_hex(std::string_view s)
{
    if (s.size() >= 2 && s[0] == '0' && s[1] == 'x') {
        s.remove_prefix(2);
    }

    byte_string r((s.size() + 1) / 2, (unsigned char)0);
    unsigned in = 0, out = 0;
    // handle odd nibbles
    if (s.size() % 2) {
        r[out++] = from_hex_digit(s[in++]);
    }
    bool odd = true;
    unsigned char hi_nibble;

    for (; in < s.size(); ++in) {
        auto const v = from_hex_digit(s[in]);
        if (v == 0xff) {
            // invalid input, return empty
            return {};
        }
        if (odd) {
            hi_nibble = static_cast<unsigned char>(v << 4);
        }
        else {
            r[out++] = hi_nibble | v;
        }

        odd = !odd;
    }

    return r;
}

namespace literals
{
    constexpr byte_string operator""_hex(char const *s) noexcept
    {
        return from_hex(s);
    }
};

MONAD_NAMESPACE_END
