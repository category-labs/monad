#pragma once

#include <monad/core/assert.h>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <tl/optional.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

// return the key that the update would have if inserted into storage and if the
// leaf already exists
template <typename TCursor>
[[nodiscard]] constexpr std::pair<Nibbles, bool>
get_trie_key_of_leaf(Nibbles const &key, TCursor &leaves_cursor)
{
    MONAD_DEBUG_ASSERT(!leaves_cursor.empty());

    leaves_cursor.lower_bound(key);
    auto const lb = leaves_cursor.key();

    auto const exists = lb.transform(&TCursor::Key::path) == key;

    leaves_cursor.prev();
    auto const prev = leaves_cursor.key();

    auto const left = leaves_cursor.key().and_then(
        [&](auto const &prev) -> tl::optional<uint8_t> {
            return longest_common_prefix_size(prev.path(), key);
        });

    auto const right =
        lb.and_then([&](auto const &lb) -> tl::optional<uint8_t> {
            if (lb.path() == key) {
                leaves_cursor.next();
                MONAD_ASSERT(leaves_cursor.key() == lb);

                leaves_cursor.next();

                return leaves_cursor.key().and_then(
                    [&](auto const &next) -> tl::optional<uint8_t> {
                        return longest_common_prefix_size(next.path(), key);
                    });
            }
            return longest_common_prefix_size(lb.path(), key);
        });

    // Nothing to the left or right, we are updating the only
    // leaf in the trie
    if (!left && !right) {
        return std::make_pair(Nibbles{}, exists);
    }

    // key is parent path + branch (prefix of trie is invisible here)
    return std::make_pair(
        Nibbles{key.prefix(std::max(left.value_or(0), right.value_or(0)) + 1)},
        exists);
}

MONAD_TRIE_NAMESPACE_END
