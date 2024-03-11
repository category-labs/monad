#pragma once

#include <monad/config.hpp>

#define MONAD_RPC_NAMESPACE_BEGIN                                               \
    MONAD_NAMESPACE_BEGIN namespace rpc                                         \
    {

#define MONAD_RPC_NAMESPACE_END                                                 \
    }                                                                          \
    MONAD_NAMESPACE_END
