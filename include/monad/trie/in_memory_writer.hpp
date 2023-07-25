#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>

#include <algorithm>
#include <iomanip>
#include <map>
#include <unordered_set>

MONAD_TRIE_NAMESPACE_BEGIN

template <typename TComparator>
struct InMemoryWriter
{
    using storage_t = std::map<byte_string, byte_string, TComparator>;
    using set_t = std::unordered_set<byte_string, byte_string_hasher>;

    storage_t &storage;
    storage_t upserts;
    set_t prefix_deletions;
    set_t deletions;

    explicit constexpr InMemoryWriter(storage_t &s)
        : storage(s)
    {
    }

    void put(KeyBuffer const &key, byte_string_view value)
    {
        // puts should override any previous actions
        auto const bs = byte_string{key.view()};
        upserts[bs] = value;
        deletions.erase(bs);

        MONAD_DEBUG_ASSERT(
            std::ranges::none_of(prefix_deletions, [&](auto const &prefix) {
                return bs.starts_with(prefix);
            }));
    }

    void del(KeyBuffer const &key) { deletions.emplace(key.view()); }

    void del_prefix(byte_string_view prefix)
    {
        prefix_deletions.emplace(prefix);
    }

    void write()
    {
        upserts.merge(storage);

        for (auto const &prefix : prefix_deletions) {
            std::erase_if(upserts, [&](auto const &key) {
                return key.first.starts_with(prefix);
            });
        }

        for (auto const &key : deletions) {
            upserts.erase(key);
        }

        storage.swap(upserts);

        upserts.clear();
        prefix_deletions.clear();
        deletions.clear();
    }
};

MONAD_TRIE_NAMESPACE_END
