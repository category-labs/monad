#pragma once

#include <monad/config.hpp>

#include <monad/state2/state_deltas.hpp>

MONAD_NAMESPACE_BEGIN

template <class Mutex>
struct BlockState
{
    Mutex mutex;
    StateDeltas state;
    Code code;
};

MONAD_NAMESPACE_END
