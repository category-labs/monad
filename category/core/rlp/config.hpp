#pragma once

#include <category/core/config.hpp>

#define MONAD_RLP_NAMESPACE_BEGIN                                              \
    MONAD_NAMESPACE_BEGIN namespace rlp                                        \
    {

#define MONAD_RLP_NAMESPACE_END                                                \
    }                                                                          \
    MONAD_NAMESPACE_END

#define MONAD_RLP_ANONYMOUS_NAMESPACE_BEGIN                                    \
    MONAD_RLP_NAMESPACE_BEGIN                                                  \
    namespace                                                                  \
    {

#define MONAD_RLP_ANONYMOUS_NAMESPACE_END                                      \
    }                                                                          \
    MONAD_RLP_NAMESPACE_END
