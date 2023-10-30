#pragma once

#include <monad/config.hpp>

#include <monad/state2/state_deltas.hpp>

#include <boost/thread/null_mutex.hpp>

MONAD_NAMESPACE_BEGIN

struct BlockState
{
    using Mutex = boost::null_mutex;

    Mutex mutex;
    StateDeltas state;
    Code code;
};

MONAD_NAMESPACE_END
