#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>

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
    auto const size_is_odd = nibbles.nibble_size() % 2;

    MONAD_DEBUG_ASSERT(nibbles.nibble_size() || terminating);

    // Populate first byte with the encoded nibbles type and potentially
    // also the first nibble if number of nibbles is odd
    res[0] = terminating ? 0x20 : 0x00;
    if (size_is_odd) {
        res[0] |= static_cast<unsigned char>(0x10 | nibbles.get(0));
    }

    // at this point destination is byte aligned and remaining number of nibbles
    // is even
    if (size_is_odd == nibbles.begin_nibble_) {
        // source is byte aligned can use simple copy
        auto const end = std::copy(
            nibbles.data_ + size_is_odd,
            nibbles.data_ + nibbles.data_size(),
            res + 1);

        return {res, end};
    }
    else {
        // copy from unaligned source to aligned destination
        auto np = nibbles.data_;
        auto res_p = res + 1;
        // last byte has single nibble, stop after processing previous byte
        auto const end = nibbles.data_ + nibbles.data_size() - 1;
        for (; np < end; ++np, ++res_p) {
            *res_p = static_cast<unsigned char>((*np << 4) | (*(np + 1) >> 4));
        }
        return {res, res_p};
    }
}

MONAD_MPT_NAMESPACE_END
