#pragma once

#include <monad/config.hpp>

#define MONAD_IO_NAMESPACE_BEGIN                                               \
    MONAD_NAMESPACE_BEGIN namespace io                                         \
    {

#define MONAD_IO_NAMESPACE_END                                                 \
    }                                                                          \
    MONAD_NAMESPACE_END
