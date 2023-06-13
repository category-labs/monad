#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <variant>

MONAD_TRIE_NAMESPACE_BEGIN

struct Upsert
{
    Nibbles key;
    byte_string value;
};

struct Delete
{
    Nibbles key;
};

using Update = std::variant<Upsert, Delete>;

MONAD_TRIE_NAMESPACE_END
