#pragma once

#define MONAD_NAMESPACE_BEGIN                                                  \
    namespace monad                                                            \
    {

#define MONAD_NAMESPACE_END }

#define MONAD_ANONYMOUS_NAMESPACE_BEGIN                                        \
    namespace monad                                                            \
    {                                                                          \
        namespace                                                              \
        {

#define MONAD_ANONYMOUS_NAMESPACE_END                                          \
    }                                                                          \
    }
