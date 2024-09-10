#pragma once

#include <monad/core/likely.h>
#include <stdarg.h>

#ifdef __cplusplus
extern "C"
{
#endif

[[noreturn]] void monad_vabort(
    char const *function, char const *file, long line, char const *format,
    va_list ap);

[[noreturn]] static inline void monad_abort(
    char const *function, char const *file, long line, char const *format, ...)
{
    va_list ap;
    va_start(ap, format);
    monad_vabort(function, file, line, format, ap);
    va_end(ap);
}

[[noreturn]] void monad_assertion_failed(
    char const *expr, char const *function, char const *file, long line);

#define MONAD_ABORT(FORMAT, ...)                                               \
    monad_abort(                                                               \
        __extension__ __PRETTY_FUNCTION__,                                     \
        __FILE__,                                                              \
        __LINE__,                                                              \
        FORMAT __VA_OPT__(, ) __VA_ARGS__)

#define MONAD_ASSERT(expr)                                                     \
    if (MONAD_LIKELY(expr)) { /* likeliest */                                  \
    }                                                                          \
    else {                                                                     \
        monad_assertion_failed(                                                \
            #expr, __extension__ __PRETTY_FUNCTION__, __FILE__, __LINE__);     \
    }

#ifdef NDEBUG
    #define MONAD_DEBUG_ASSERT(x)                                              \
        do {                                                                   \
            (void)sizeof(x);                                                   \
        }                                                                      \
        while (0)
#else
    #define MONAD_DEBUG_ASSERT(x) MONAD_ASSERT(x)
#endif

#ifdef __cplusplus
}
#endif
