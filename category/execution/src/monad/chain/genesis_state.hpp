#pragma once

#include <category/core/config.hpp>
#include <monad/core/block.hpp>

MONAD_NAMESPACE_BEGIN

class TrieDb;

struct GenesisState
{
    BlockHeader header{};
    char const *const alloc{nullptr};
};

void load_genesis_state(GenesisState const &, TrieDb &);

MONAD_NAMESPACE_END
