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

bool can_merge(StateDeltas const &to, StateDeltas const &from);
void merge(StateDeltas &to, StateDeltas const &from);

void merge(Code &to, Code &from);

MONAD_NAMESPACE_END
