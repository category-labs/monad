#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles_view.hpp>

#include <cassert>

MONAD_TRIE_NAMESPACE_BEGIN

// Transform the nibbles to its compact encoding
// https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
[[nodiscard]] constexpr byte_string
compact_encode(NibblesView const &nibbles, bool is_leaf)
{
    size_t i = 0;

    byte_string bytes;

    // Populate first byte with the encoded nibbles type and potentially
    // also the first nibble if number of nibbles is odd
    auto const first_byte = [&]() -> byte_string::value_type {
        if (is_leaf) {
            if (nibbles.size() % 2) {
                auto const first_byte =
                    static_cast<byte_string::value_type>(0x30 | nibbles[i]);
                ++i;
                return first_byte;
            }
            else {
                return 0x20;
            }
        }
        else {
            if (nibbles.size() % 2) {
                auto const first_byte =
                    static_cast<byte_string::value_type>(0x10 | nibbles[i]);
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
        bytes.push_back(static_cast<byte_string::value_type>(
            (nibbles[i] << 4) | nibbles[i + 1]));
    }

    return bytes;
}

MONAD_TRIE_NAMESPACE_END
