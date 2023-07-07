#pragma once

#include <monad/config.hpp>

#define MONAD_STATE_NAMESPACE_BEGIN                                            \
    MONAD_NAMESPACE_BEGIN namespace state                                      \
    {

#define MONAD_STATE_NAMESPACE_END                                              \
    }                                                                          \
    MONAD_NAMESPACE_END
