#pragma once

#include <monad/core/address.hpp>
#include <monad/trie/comparator.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

struct InMemoryPathComparator
{
    [[nodiscard]] inline bool
    operator()(byte_string_view element, byte_string_view value) const
    {
        return path_compare(element, value) < 0;
    }
};

struct InMemoryPrefixPathComparator
{
    [[nodiscard]] inline bool
    operator()(byte_string_view element, byte_string_view value) const
    {
        assert(element.size() > sizeof(address_t));
        assert(value.size() > sizeof(address_t));

        auto const rc =
            std::memcmp(element.data(), value.data(), sizeof(address_t));
        if (rc != 0) {
            return rc < 0;
        }

        element.remove_prefix(sizeof(address_t));
        value.remove_prefix(sizeof(address_t));

        return path_compare(element, value) < 0;
    }
};

MONAD_TRIE_NAMESPACE_END
