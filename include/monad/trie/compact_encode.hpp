#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <cassert>

MONAD_TRIE_NAMESPACE_BEGIN

// Transform the nibbles to its compact encoding
// https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
constexpr byte_string compact_encode(Nibbles const &nibbles, bool is_leaf)
{
    assert(not nibbles.empty());

    size_t i = 0;

    byte_string bytes;

    // Populate first byte with the encoded nibbles type and potentially
    // also the first nibble if number of nibbles is odd
    auto const first_byte = [&]() {
        if (is_leaf) {
            if (nibbles.is_odd) {
                auto const first_byte = 0x30 | nibbles[i];
                ++i;
                return first_byte;
            }
            else {
                return 0x20;
            }
        }
        else {
            if (nibbles.is_odd) {
                auto const first_byte = 0x10 | nibbles[i];
                ++i;
                return first_byte;
            }
            else {
                return 0x00;
            }
        }
    }();

    bytes.push_back(first_byte);

    // should be an even number of hops away from the end
    assert(((nibbles.size() - i) % 2) == 0);

    for (; i < nibbles.size(); i += 2) {
        bytes.push_back((nibbles[i] << 4) | nibbles[i + 1]);
    }

    return bytes;
}

MONAD_TRIE_NAMESPACE_END
