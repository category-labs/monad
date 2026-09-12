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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/rlp/config.hpp>

#include <concepts>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string const EMPTY_STRING = {0x80};

inline byte_string_view zeroless_view(byte_string_view const string_view)
{
    auto const *b = string_view.begin();
    auto const *e = string_view.end();
    while (b < e && *b == 0) {
        ++b;
    }
    return {b, e};
}

inline byte_string to_big_compact(unsigned_integral auto n)
{
    n = bswap(n);
    return byte_string(
        zeroless_view({reinterpret_cast<unsigned char *>(&n), sizeof(n)}));
}

// Size helpers and cursor-based writers avoid temporary nested encodings.
// Writers require enough space, as computed by the matching size helpers.

// Built-in unsigned types only; wider integers use separate overloads.
inline size_t big_compact_size(std::unsigned_integral auto const byte_count)
{
    return (static_cast<size_t>(std::bit_width(byte_count)) + 7) / 8;
}

// The length of the header encode_list2 writes ahead of encoded_item payload
// this size.
inline size_t list_header_size(size_t const payload)
{
    return payload > 55 ? 1 + big_compact_size(payload) : 1;
}

// encode_string2's length, header included.
inline size_t encoded_string_size(byte_string_view const string_view)
{
    size_t const size = string_view.size();
    if (size == 1 && string_view[0] <= 0x7f) {
        return 1;
    }
    return (size > 55 ? 1 + big_compact_size(size) : 1) + size;
}

// Append the long-form prefix and big-endian payload length.
inline void append_length(
    unsigned char *&cursor, unsigned char const base, size_t const size)
{
    size_t const byte_count = big_compact_size(size);
    *cursor++ = static_cast<unsigned char>(base + byte_count);
    for (size_t i = byte_count; i-- > 0;) {
        *cursor++ = static_cast<unsigned char>(size >> (i * 8));
    }
}

// encode_list2's header, written ahead of encoded_item payload the caller owns.
inline void append_list_header(unsigned char *&cursor, size_t const payload)
{
    if (payload > 55) {
        append_length(cursor, 0xf7, payload);
        return;
    }
    *cursor++ = static_cast<unsigned char>(0xc0 + payload);
}

// encode_string2, appended rather than returned.
inline void
append_string2(unsigned char *&cursor, byte_string_view const string_view)
{
    size_t const size = string_view.size();
    if (size == 1 && string_view[0] <= 0x7f) {
        *cursor++ = string_view[0];
        return;
    }
    if (size > 55) {
        append_length(cursor, 0xb7, size);
    }
    else {
        *cursor++ = static_cast<unsigned char>(0x80 + size);
    }
    std::memcpy(cursor, string_view.data(), size);
    cursor += size;
}

inline byte_string encode_string2(byte_string_view const string_view)
{
    byte_string result;
    result.resize_and_overwrite(
        encoded_string_size(string_view),
        [string_view](unsigned char *const buffer, size_t const byte_count) {
            unsigned char *cursor = buffer;
            append_string2(cursor, string_view);
            MONAD_ASSERT(cursor == buffer + byte_count);
            return byte_count;
        });
    return result;
}

template <std::convertible_to<byte_string>... Args>
byte_string encode_list2(Args const &...args)
{
    size_t const payload = (args.size() + ... + size_t{0});

    byte_string result;
    result.resize_and_overwrite(
        list_header_size(payload) + payload,
        [&](unsigned char *const buffer, size_t const byte_count) {
            unsigned char *cursor = buffer;
            append_list_header(cursor, payload);
            [[maybe_unused]] auto const append_encoded =
                [&cursor](auto const &encoded_item) {
                    // Encoded RLP, not a string: nothing to NUL-terminate.
                    // NOLINTNEXTLINE(bugprone-not-null-terminated-result)
                    std::memcpy(
                        cursor, encoded_item.data(), encoded_item.size());
                    cursor += encoded_item.size();
                };
            (append_encoded(args), ...);
            MONAD_ASSERT(cursor == buffer + byte_count);
            return byte_count;
        });
    return result;
}

MONAD_RLP_NAMESPACE_END
