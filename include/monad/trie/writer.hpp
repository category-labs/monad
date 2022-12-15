#pragma once

#include <cstdint>
#include <monad/trie/config.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

// TODO: figure out how to do this better so that we dont have to specify
// WriterColumn
enum class WriterColumn : uint8_t
{
    ACCOUNT_LEAVES = 0,
    STORAGE_LEAVES = 1,
    ACCOUNT_ALL = 2,
    STORAGE_ALL = 3
};

MONAD_TRIE_NAMESPACE_END
