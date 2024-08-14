#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>

#include <array>
#include <cassert>

MONAD_MPT_NAMESPACE_BEGIN

constexpr size_t max_compact_encode_size = KECCAK256_SIZE + 1;
using CompactEncodeRes = std::array<unsigned char, max_compact_encode_size>;

inline constexpr unsigned
compact_encode_len(unsigned const si, unsigned const ei)
{
    MONAD_DEBUG_ASSERT(ei >= si);
    return (ei - si) / 2 + 1;
}

// Transform the nibbles to its compact encoding
// https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
[[nodiscard]] constexpr byte_string_view compact_encode(
    CompactEncodeRes &res, NibblesView const nibbles, bool const terminating)
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
        set_nibble(res.data(), res_ci++, nibbles.get(i));
    }

    return byte_string_view{
        res.data(),
        nibbles.nibble_size() ? (nibbles.nibble_size() / 2 + 1) : 1u};
}

MONAD_MPT_NAMESPACE_END
