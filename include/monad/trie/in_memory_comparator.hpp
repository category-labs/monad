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
        assert(element.size() > sizeof(Address));
        assert(value.size() > sizeof(Address));

        auto const rc =
            std::memcmp(element.data(), value.data(), sizeof(Address));
        if (rc != 0) {
            return rc < 0;
        }

        element.remove_prefix(sizeof(Address));
        value.remove_prefix(sizeof(Address));

        return path_compare(element, value) < 0;
    }
};

MONAD_TRIE_NAMESPACE_END
