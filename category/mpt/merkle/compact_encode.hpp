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
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cassert>

MONAD_MPT_NAMESPACE_BEGIN

inline constexpr unsigned
compact_encode_len(unsigned const si, unsigned const ei)
{
    MONAD_DEBUG_ASSERT(ei >= si);
    return (ei - si) / 2 + 1;
}

// Transform the nibbles to its compact encoding
// https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
[[nodiscard]] constexpr byte_string_view compact_encode(
    unsigned char *const res, NibblesView const nibbles, bool const terminating)
{
    unsigned i = 0;

    MONAD_DEBUG_ASSERT(nibbles.nibble_size() || terminating);

    // Populate first byte with the encoded nibbles type and potentially
    // also the first nibble if number of nibbles is odd
    res[0] = terminating ? 0x20 : 0x00;
    if (nibbles.nibble_size() % 2) {
        res[0] |= static_cast<unsigned char>(0x10 | nibbles.get(0));
        i = 1;
    }

    unsigned res_ci = 2;
    for (; i < nibbles.nibble_size(); i++) {
        set_nibble(res, res_ci++, nibbles.get(i));
    }

    return byte_string_view{
        res, nibbles.nibble_size() ? (nibbles.nibble_size() / 2 + 1) : 1u};
}

MONAD_MPT_NAMESPACE_END
