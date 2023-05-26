#pragma once

#include <algorithm>
#include <unordered_map>
#include <vector>

#include <monad/trie/comparator.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/writer.hpp>

#include <monad/core/byte_string.hpp>
#include <tl/optional.hpp>

#include <iomanip>
#include <ostream>

MONAD_TRIE_NAMESPACE_BEGIN

struct InMemoryWriter
{
    using element_t = std::pair<byte_string, byte_string>;
    using storage_t = std::vector<element_t>;
    using changes_t = std::unordered_map<
        byte_string, tl::optional<byte_string>, byte_string_hasher>;

    std::unordered_map<WriterColumn, std::reference_wrapper<storage_t>>
        storages_;
    std::unordered_map<WriterColumn, changes_t> changes_;
    std::unordered_map<WriterColumn, std::vector<byte_string>>
        deleted_prefixes_;

    constexpr void
    put(WriterColumn col, KeyBuffer const &key, byte_string_view value)
    {
        changes_[col][byte_string{key.view()}] = value;
    }

    constexpr void del(WriterColumn col, KeyBuffer const &key)
    {
        changes_[col][byte_string{key.view()}] = tl::nullopt;
    }

    void del_prefix(WriterColumn col, byte_string_view prefix)
    {
        deleted_prefixes_[col].emplace_back(prefix);

        if (auto it = changes_.find(col); it != changes_.end()) {
            std::erase_if(it->second, [&](auto const &key) {
                return key.first.starts_with(prefix);
            });
        }
    }

    template <typename... DummyArgs>
        requires(sizeof...(DummyArgs) == 0)
    void write()
    {
        // Delete the prefixes first
        for (auto const &[col, prefixes] : deleted_prefixes_) {
            for (auto const &prefix : prefixes) {
                std::erase_if(storages_.at(col).get(), [&](auto const &key) {
                    return key.first.starts_with(prefix);
                });
            }
        }

        // Apply changes second
        for (auto const &[col, changes] : changes_) {
            auto &storage = storages_.at(col).get();
            for (auto const &change : changes) {
                [[maybe_unused]] auto const num =
                    std::erase_if(storage, [&](auto const &p) {
                        return p.first == change.first;
                    });

                assert(num <= 1);

                if (change.second) {
                    storage.emplace_back(change.first, *change.second);
                }
            }

            comparator auto const cmp = injected_comparator<DummyArgs...>;
            std::ranges::sort(storage, cmp, &element_t::first);
        }

        changes_.clear();
        deleted_prefixes_.clear();
    }
};

MONAD_TRIE_NAMESPACE_END
