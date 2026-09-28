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
#include <category/core/result.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cassert>
#include <limits>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

// Hex-prefix ("compact") encoding of a node path. For 4-bit symbols this is
// the Ethereum encoding: flag byte (0x20 terminating, 0x10 odd length, low
// nibble = first symbol when odd) followed by the remaining symbols two per
// byte. For wider symbols the same flag byte (0x20 terminating, 0x10 odd
// symbol count) is followed by the symbols bit-packed MSB-first; the odd flag
// disambiguates the symbol count, since a given byte length holds at most two
// consecutive counts.
constexpr unsigned compact_encode_len(unsigned const si, unsigned const ei)
{
    MONAD_ASSERT(ei >= si);
    if constexpr (NIBBLE_BITS == 4) {
        return (ei - si) / 2 + 1;
    }
    else {
        return 1 + bytes_for_nibbles(ei - si);
    }
}

constexpr void compact_encode_raw(
    unsigned char *const res, NibblesView const nibbles, bool const terminating)
{
    MONAD_ASSERT(nibbles.nibble_size() || terminating);

    res[0] = terminating ? 0x20 : 0x00;
    if constexpr (NIBBLE_BITS == 4) {
        unsigned i = 0;
        // Populate first byte with the encoded nibbles type and potentially
        // also the first nibble if number of nibbles is odd
        if (nibbles.nibble_size() % 2) {
            res[0] |= static_cast<unsigned char>(0x10 | nibbles.get(0));
            i = 1;
        }
        unsigned res_ci = 2;
        for (; i < nibbles.nibble_size(); i++) {
            set_nibble(res, res_ci, nibbles.get(i));
            ++res_ci;
        }
    }
    else {
        if (nibbles.nibble_size() % 2) {
            res[0] |= 0x10;
        }
        unsigned const bytes = bytes_for_nibbles(nibbles.nibble_size());
        for (unsigned i = 0; i < bytes; ++i) {
            res[1 + i] = 0;
        }
        for (unsigned i = 0; i < nibbles.nibble_size(); i++) {
            detail::set_symbol(res + 1, 0, i, nibbles.get(i));
        }
    }
}

[[nodiscard]] constexpr byte_string_view compact_encode(
    unsigned char *const res, NibblesView const nibbles, bool const terminating)
{
    compact_encode_raw(res, nibbles, terminating);
    return byte_string_view{res, compact_encode_len(0, nibbles.nibble_size())};
}

[[nodiscard]] inline Result<std::pair<Nibbles, bool>>
compact_decode(byte_string_view const enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return rlp::DecodeError::InputTooShort;
    }

    // High two bits of the prefix byte must be zero (valid range 0x00–0x3F).
    if (MONAD_UNLIKELY(enc[0] & 0xC0)) {
        return rlp::DecodeError::TypeUnexpected;
    }

    bool const terminating = enc[0] & 0x20;
    bool const odd = enc[0] & 0x10;

    size_t nibble_count = 0;
    if constexpr (NIBBLE_BITS == 4) {
        // For even-length paths the low nibble of the prefix is padding and
        // must be zero.
        if (MONAD_UNLIKELY(!odd && (enc[0] & 0x0F))) {
            return rlp::DecodeError::TypeUnexpected;
        }
        nibble_count = (enc.size() - 1) * 2 + static_cast<size_t>(odd);
    }
    else {
        if (MONAD_UNLIKELY(enc[0] & 0x0F)) {
            return rlp::DecodeError::TypeUnexpected;
        }
        // the largest symbol count that fits the payload, or one less when
        // the parity flag says so
        size_t const payload_bits = (enc.size() - 1) * 8;
        nibble_count = payload_bits / NIBBLE_BITS;
        if ((nibble_count % 2 != 0) != odd) {
            if (MONAD_UNLIKELY(nibble_count == 0)) {
                return rlp::DecodeError::TypeUnexpected;
            }
            --nibble_count;
        }
        if (MONAD_UNLIKELY(
                nibble_count > 0 && bytes_for_nibbles(static_cast<unsigned>(
                                        nibble_count)) != enc.size() - 1)) {
            return rlp::DecodeError::TypeUnexpected;
        }
    }

    // A non-terminating (extension) node with an empty path is structurally
    // invalid — compact_encode asserts against it, so reject here to keep
    // decode/encode symmetric.
    if (MONAD_UNLIKELY(nibble_count == 0 && !terminating)) {
        return rlp::DecodeError::PathTooShort;
    }

    if (MONAD_UNLIKELY(nibble_count > std::numeric_limits<uint8_t>::max())) {
        return rlp::DecodeError::PathTooLong;
    }

    Nibbles result{nibble_count};

    if constexpr (NIBBLE_BITS == 4) {
        size_t nibble_i = 0;
        if (odd) {
            result.set(static_cast<unsigned>(nibble_i++), enc[0] & 0x0F);
        }
        for (size_t i = 1; i < enc.size(); ++i) {
            result.set(static_cast<unsigned>(nibble_i++), enc[i] >> 4);
            result.set(static_cast<unsigned>(nibble_i++), enc[i] & 0x0F);
        }
    }
    else {
        for (unsigned i = 0; i < nibble_count; ++i) {
            result.set(
                i,
                detail::get_symbol(
                    enc.data() + 1,
                    0,
                    i,
                    static_cast<unsigned>(enc.size() - 1)));
        }
    }

    return std::pair{std::move(result), terminating};
}

MONAD_MPT_NAMESPACE_END
