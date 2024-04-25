#pragma once

#include <monad/config.hpp>

#define MONAD_FIBER_NAMESPACE_BEGIN                                            \
    MONAD_NAMESPACE_BEGIN namespace fiber                                      \
    {

#define MONAD_FIBER_NAMESPACE_END                                              \
    }                                                                          \
    MONAD_NAMESPACE_END
