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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

std::optional<byte_string> from_hex(std::string_view hex)
{
    auto ret = byte_string{};

    skip_optional_hex_prefix(hex);

    if (hex.size() % 2 != 0) {
        return std::nullopt;
    }

    size_t const input_bytes = hex.size() / 2;
    ret.reserve(input_bytes);

    for (size_t i = 0; i < input_bytes; ++i) {
        uint8_t byte;
        if (!parse_hex_byte(hex, byte)) {
            return std::nullopt;
        }
        ret.push_back(byte);
    }

    return ret;
}

std::string to_hex(uint8_t const byte)
{
    uint8_t const high = byte >> 4;
    uint8_t const low = byte & 0x0F;
    return std::string{to_hex_char(high), to_hex_char(low)};
}

std::string to_hex(byte_string_view const bytes)
{
    auto ret = std::string{};
    ret.reserve(bytes.size() * 2);

    for (auto const byte : bytes) {
        ret += to_hex_char(byte >> 4);
        ret += to_hex_char(byte & 0x0F);
    }

    return ret;
}

namespace literals
{
    byte_string operator""_bytes(char const *const s)
    {
        return from_hex(s).value();
    }
}

MONAD_NAMESPACE_END
