#pragma once

#include <monad/core/byte_string.hpp>

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
