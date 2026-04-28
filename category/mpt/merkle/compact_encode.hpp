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

inline constexpr unsigned
compact_encode_len(unsigned const si, unsigned const ei)
{
    MONAD_ASSERT(ei >= si);
    return (ei - si) / 2 + 1;
}

// Transform the nibbles to its compact encoding
// https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
[[nodiscard]] constexpr byte_string_view compact_encode(
    unsigned char *const res, NibblesView const nibbles, bool const terminating)
{
    unsigned i = 0;

    MONAD_ASSERT(nibbles.nibble_size() || terminating);

    // Populate first byte with the encoded nibbles type and potentially
    // also the first nibble if number of nibbles is odd
    res[0] = terminating ? 0x20 : 0x00;
    if (nibbles.nibble_size() % 2) {
        res[0] |= static_cast<unsigned char>(0x10 | nibbles.get(0));
        i = 1;
    }

    unsigned res_ci = 2;
    for (; i < nibbles.nibble_size(); i++) {
        set_nibble(res, res_ci, nibbles.get(i));
        ++res_ci;
    }

    return byte_string_view{
        res, nibbles.nibble_size() ? (nibbles.nibble_size() / 2 + 1) : 1u};
}

// Decode a compact-encoded path.
// Returns {nibbles, is_leaf} on success, or an rlp::DecodeError if enc is
// empty or otherwise invalid.
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

    // For even-length paths the low nibble of the prefix is padding and must
    // be zero.
    if (MONAD_UNLIKELY(!odd && (enc[0] & 0x0F))) {
        return rlp::DecodeError::TypeUnexpected;
    }

    size_t const nibble_count = (enc.size() - 1) * 2 + static_cast<size_t>(odd);

    // A non-terminating (extension) node with an empty path is structurally
    // invalid — compact_encode asserts against it, so reject here to keep
    // decode/encode symmetric.
    if (MONAD_UNLIKELY(nibble_count == 0 && !terminating)) {
        return rlp::DecodeError::PathTooShort;
    }

    // Nibbles uses uint8_t for length; reject inputs that would overflow it.
    if (MONAD_UNLIKELY(nibble_count > std::numeric_limits<uint8_t>::max())) {
        return rlp::DecodeError::PathTooLong;
    }

    Nibbles result{nibble_count};

    size_t nibble_i = 0;
    if (odd) {
        result.set(static_cast<unsigned>(nibble_i++), enc[0] & 0x0F);
    }
    for (size_t i = 1; i < enc.size(); ++i) {
        result.set(static_cast<unsigned>(nibble_i++), enc[i] >> 4);
        result.set(static_cast<unsigned>(nibble_i++), enc[i] & 0x0F);
    }

    return std::pair{std::move(result), terminating};
}

MONAD_MPT_NAMESPACE_END
