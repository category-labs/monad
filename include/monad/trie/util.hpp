#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

constexpr byte_string_view::value_type
get_nibble(byte_string_view rep, size_t i)
{
    return (i % 2) == 0 ? rep.at(i / 2 + 1) >> 4 : rep.at(i / 2 + 1) & 0x0F;
}

MONAD_TRIE_NAMESPACE_END
