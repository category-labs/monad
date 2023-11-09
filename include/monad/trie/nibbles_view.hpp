#pragma once

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/util.hpp>

#include <cassert>

MONAD_TRIE_NAMESPACE_BEGIN

struct NibblesView
{
    byte_string_view rep;
    uint8_t start; // starting nibble index
    uint8_t len; // length of nibbles

    constexpr NibblesView(byte_string_view rep, uint8_t start, uint8_t len)
        : rep(rep)
        , start(start)
        , len(len)
    {
    }

    [[nodiscard]] constexpr uint8_t size() const
    {
        return len;
    }

    [[nodiscard]] constexpr bool empty() const
    {
        return size() == 0;
    }

    [[nodiscard]] constexpr byte_string::value_type operator[](size_t i) const
    {
        assert(i < len);
        return get_nibble(rep, i + start);
    }

    [[nodiscard]] constexpr bool operator==(NibblesView const &other) const
    {
        if (size() != other.size()) {
            return false;
        }

        for (size_t i = 0; i < size(); ++i) {
            if ((*this)[i] != other[i]) {
                return false;
            }
        }
        return true;
    }
};

static_assert(sizeof(NibblesView) == 24);

MONAD_TRIE_NAMESPACE_END
