#pragma once

#include <algorithm>
#include <unordered_map>
#include <vector>

#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>

#include <monad/core/byte_string.hpp>
#include <tl/optional.hpp>

#include <iomanip>
#include <ostream>

MONAD_TRIE_NAMESPACE_BEGIN

template <typename TComparator>
struct InMemoryWriter
{
    using element_t = std::pair<byte_string, byte_string>;
    using storage_t = std::vector<element_t>;
    using changes_t = std::unordered_map<
        byte_string, tl::optional<byte_string>, byte_string_hasher>;

    storage_t &storage;
    changes_t changes;
    std::vector<byte_string> deleted_prefixes;

    explicit constexpr InMemoryWriter(storage_t &s)
        : storage(s)
    {
    }

    void put(KeyBuffer const &key, byte_string_view value)
    {
        changes[byte_string{key.view()}] = value;
    }

    void del(KeyBuffer const &key)
    {
        changes[byte_string{key.view()}] = tl::nullopt;
    }

    void del_prefix(byte_string_view prefix)
    {
        deleted_prefixes.emplace_back(prefix);

        std::erase_if(changes, [&](auto const &key) {
            return key.first.starts_with(prefix);
        });
    }

    void write()
    {
        // Delete the prefixes first
        for (auto const &prefix : deleted_prefixes) {
            std::erase_if(storage, [&](auto const &key) {
                return key.first.starts_with(prefix);
            });
        }

        // Apply changes second
        for (auto const &change : changes) {
            auto const num = std::erase_if(storage, [&](auto const &p) {
                return p.first == change.first;
            });

            MONAD_DEBUG_ASSERT(num <= 1);

            if (change.second.has_value()) {
                storage.emplace_back(change.first, change.second.value());
            }

            std::ranges::sort(storage, TComparator{}, &element_t::first);
        }

        changes.clear();
        deleted_prefixes.clear();
    }
};

MONAD_TRIE_NAMESPACE_END
