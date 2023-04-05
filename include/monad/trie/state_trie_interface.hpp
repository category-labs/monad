#pragma once

#include <monad/db/state_db.hpp>
#include <monad/trie/config.hpp>

#include <concepts>

MONAD_TRIE_NAMESPACE_BEGIN

template <class TState>
class IStateTrie
{
public:
    virtual void incremental_update(TState &state) = 0;
};

MONAD_TRIE_NAMESPACE_END