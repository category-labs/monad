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
#include <category/core/bit_primitives.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cassert>
#include <cstdint>
#include <cstring>
#include <limits>
#include <type_traits>
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
constexpr void compact_encode_raw(
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

    // What is left is always an even nibble count landing byte-aligned in
    // res (destination nibble 2 = res[1]), so it is a byte run, not a
    // nibble run: either a straight copy or one uniform 4-bit shift,
    // depending on whether the source run starts mid-byte.
    if (std::is_constant_evaluated()) {
        unsigned res_ci = 2;
        for (; i < nibbles.nibble_size(); i++) {
            set_nibble(res, res_ci, nibbles.get(i));
            ++res_ci;
        }
        return;
    }

    unsigned const m = nibbles.nibble_size() - i;
    unsigned const s = nibbles.begin_nibble() + i; // source nibble index
    unsigned char const *const src = nibbles.data() + s / 2;

    if (s % 2 == 0) {
        std::memcpy(res + 1, src, m / 2);
    }
    else {
        // A 4-bit left shift of the byte run, which is a funnel shift eight
        // output bytes at a time rather than two loads, two shifts, an or and
        // a byte store apiece. Leaf paths here are the unconsumed tail of a
        // hashed key and so run near the full 32 bytes, which is what makes
        // the wide form worth having.
        //
        // The reads stay inside the byte loop's own bounds: the group needs
        // src[k..k+7] and src[k+8], and k + 8 <= n, while the byte loop reads
        // src[n] itself on its last turn.
        unsigned const n = m / 2;
        unsigned k = 0;
        for (; k + 8 <= n; k += 8) {
            std::uint64_t w;
            std::memcpy(&w, src + k, sizeof(w));
            std::uint64_t const be = bits::bswap64(
                (bits::bswap64(w) << 4) |
                (static_cast<std::uint64_t>(src[k + 8]) >> 4));
            std::memcpy(res + 1 + k, &be, sizeof(be));
        }
        for (; k < n; ++k) {
            res[1 + k] = static_cast<unsigned char>(
                (src[k] << 4) | (src[k + 1] >> 4));
        }
    }
}

[[nodiscard]] constexpr byte_string_view compact_encode(
    unsigned char *const res, NibblesView const nibbles, bool const terminating)
{
    compact_encode_raw(res, nibbles, terminating);
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
