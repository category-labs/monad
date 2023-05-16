#pragma once

#include <monad/config.hpp>

#define MONAD_DB_NAMESPACE_BEGIN                                               \
    MONAD_NAMESPACE_BEGIN namespace db                                         \
    {

#define MONAD_DB_NAMESPACE_END                                                 \
    }                                                                          \
    MONAD_NAMESPACE_END
