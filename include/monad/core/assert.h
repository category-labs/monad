#pragma once

#include <monad/core/likely.h>

#ifdef __cplusplus
extern "C"
{
#endif

void monad_assertion_failed(
    char const *expr, char const *function, char const *file, long line);

#ifdef __cplusplus
}
#endif

#define MONAD_ASSERT(expr)                                                     \
    (MONAD_LIKELY(!!(expr))                                                    \
         ? ((void)0)                                                           \
         : monad_assertion_failed(                                             \
               #expr, __PRETTY_FUNCTION__, __FILE__, __LINE__))

#ifdef NDEBUG
    #define MONAD_DEBUG_ASSERT(x)                                              \
        do {                                                                   \
            (void)sizeof(x);                                                   \
        }                                                                      \
        while (0)
#else
    #include <assert.h>
    #define MONAD_DEBUG_ASSERT(x) assert(x)
#endif
