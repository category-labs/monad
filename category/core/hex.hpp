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

#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>

#include <concepts>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

/// A type that contains a fixed-size `uint8_t bytes[N]` member spanning
/// the entire object (e.g. Address, Hash).  Used to constrain from_hex
/// so it can decode directly into the target's byte array.
template <typename T>
concept FixedBytes = requires(T const &t) {
    t.bytes;
    requires sizeof(T) == sizeof(t.bytes);
    requires std::is_bounded_array_v<
        std::remove_reference_t<decltype(t.bytes)>>;
    requires std::same_as<
        std::remove_extent_t<std::remove_reference_t<decltype(t.bytes)>>,
        uint8_t>;
};

/// Decode a single ASCII hex character ('0'-'9', 'a'-'f', 'A'-'F') to its
/// 4-bit numeric value.  Returns nullopt for non-hex characters.
constexpr std::optional<uint8_t> from_hex_char(char const c) noexcept
{
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    else if (c >= 'a' && c <= 'f') {
        return 10 + (c - 'a');
    }
    else if (c >= 'A' && c <= 'F') {
        return 10 + (c - 'A');
    }

    return std::nullopt;
}

/// Consume the next two hex characters from @p hex and write the decoded byte
/// to @p byte.  Returns false (and does not advance @p hex or write to @p byte)
/// if fewer than two characters remain or either character is not valid hex.
constexpr bool parse_hex_byte(std::string_view &hex, uint8_t &byte) noexcept
{
    if (hex.size() < 2) {
        return false;
    }

    auto const high = from_hex_char(hex[0]);
    auto const low = from_hex_char(hex[1]);
    if (!high.has_value() || !low.has_value()) {
        return false;
    }

    byte = static_cast<uint8_t>((*high << 4) | *low);
    hex.remove_prefix(2);

    return true;
}

/// Strip a leading "0x" prefix from @p hex, if present.
constexpr void skip_optional_hex_prefix(std::string_view &hex) noexcept
{
    if (hex.size() >= 2 && hex[0] == '0' && hex[1] == 'x') {
        hex.remove_prefix(2);
    }
}

/// Decode a hex string into a fixed-size byte type (e.g. Address, Hash).
/// The input may optionally start with "0x".  If the decoded length is shorter
/// than sizeof(T), the result is right-aligned (zero-padded on the left).
/// Returns nullopt on odd-length input, excess bytes, or invalid hex.
template <FixedBytes T>
constexpr std::optional<T> from_hex(std::string_view hex) noexcept
{
    static constexpr size_t output_bytes = sizeof(T);
    auto ret = T{};

    skip_optional_hex_prefix(hex);

    if (hex.size() % 2 != 0) {
        return std::nullopt;
    }

    size_t const input_bytes = hex.size() / 2;
    if (input_bytes > output_bytes) {
        return std::nullopt;
    }

    auto const offset = output_bytes - input_bytes;

    for (size_t i = 0; i < input_bytes; ++i) {
        if (!parse_hex_byte(hex, ret.bytes[i + offset])) {
            return std::nullopt;
        }
    }

    return ret;
}

/// Decode a hex string into a variable-length byte_string.
/// The input may optionally start with "0x".  Returns nullopt on odd-length
/// input or invalid hex characters.
std::optional<byte_string> from_hex(std::string_view hex);

/// Encode a 4-bit value (0-15) as a lowercase hex character.
/// Asserts that @p value < 16.
constexpr char to_hex_char(uint8_t const value) noexcept
{
    MONAD_ASSERT(value < 16);
    static constexpr std::string_view hex_digits = "0123456789abcdef";
    return hex_digits[value];
}

/// Encode a single byte as a two-character lowercase hex string.
std::string to_hex(uint8_t byte);

/// Encode a byte sequence as a contiguous lowercase hex string (no "0x"
/// prefix).
std::string to_hex(byte_string_view bytes);

/// Encode a FixedBytes type (e.g. Address, Hash) as a contiguous lowercase
/// hex string (no "0x" prefix), by delegating to the byte_string_view overload.
template <FixedBytes T>
std::string to_hex(T const &value)
{
    return to_hex(byte_string_view{value.bytes, sizeof(value)});
}

namespace literals
{
    /// User-defined literal for hex-encoded byte strings: `0xdeadbeef_bytes`.
    /// Throws std::bad_optional_access if the input is not valid hex.
    byte_string operator""_bytes(char const *s);
}

MONAD_NAMESPACE_END
