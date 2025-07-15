#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>

MONAD_NAMESPACE_BEGIN

class TrieDb;

struct GenesisState
{
    BlockHeader header{};
    char const *const alloc{nullptr};
};

void load_genesis_state(GenesisState const &, TrieDb &);

MONAD_NAMESPACE_END
