#pragma once

#include <monad/core/likely.h>
#include <stdarg.h>

#ifdef __cplusplus
extern "C"
{
#endif

[[noreturn]] void monad_assertion_failed_vprintf(
    char const *expr, char const *function, char const *file, long line,
    char const *format, va_list ap);

[[noreturn]] __attribute__((format(printf, 5, 6))) static inline void
monad_assertion_failed_with_msg(
    char const *expr, char const *function, char const *file, long line,
    char const *format, ...)
{
    va_list ap;
    va_start(ap, format);
    monad_assertion_failed_vprintf(expr, function, file, line, format, ap);
    va_end(ap);
}

[[noreturn]] static inline void monad_assertion_failed_no_msg(
    char const *expr, char const *function, char const *file, long line, ...)
{
    // The reason for shoehorning the "no message" assertion failure into a
    // variadic function:
    //
    //   - We have adorned the "with msg" assertion failure variant above with
    //     `__attribute__((format(...)))` to diagnose format errors at compile
    //     time
    //
    //   - Having done that, we can't call it from this function: we can't pass
    //     `nullptr` as the format, since that attribute would warn because of
    //     a non-string-literal format argument (and then -Werror kills us)
    //
    //   - Thus we can't call the "with_msg" variant from the "no_msg" variant;
    //     instead both variants must call a third va_list-style function (with
    //     no format attribute), with format == nullptr when there's no message
    va_list ap;
    va_start(ap, line);
    monad_assertion_failed_vprintf(expr, function, file, line, nullptr, ap);
    va_end(ap);
}

#define MONAD_ASSERTION_FAILED_WITH_MSG(expr, FORMAT, ...)                     \
    monad_assertion_failed_with_msg(                                           \
        expr,                                                                  \
        __extension__ __PRETTY_FUNCTION__,                                     \
        __FILE__,                                                              \
        __LINE__,                                                              \
        FORMAT __VA_OPT__(, ) __VA_ARGS__)

#define MONAD_ASSERTION_FAILED_NO_MSG(expr, ...)                               \
    monad_assertion_failed_no_msg(                                             \
        expr, __extension__ __PRETTY_FUNCTION__, __FILE__, __LINE__)

/// Assert, with backtrace upon failure; accepts an optional printf-style
/// message
#define MONAD_ASSERT(expr, ...)                                                \
    if (MONAD_LIKELY(expr)) { /* likeliest */                                  \
    }                                                                          \
    else {                                                                     \
        __VA_OPT__(MONAD_ASSERTION_FAILED_WITH_MSG(#expr, __VA_ARGS__);)       \
        __VA_OPT__(__builtin_unreachable();)                                   \
        MONAD_ASSERTION_FAILED_NO_MSG(#expr);                                  \
    }

/// Abort with a backtrace; accepts an optional printf-style message
#define MONAD_ABORT(...)                                                       \
    __VA_OPT__(MONAD_ASSERTION_FAILED_WITH_MSG(nullptr, __VA_ARGS__);)         \
    __VA_OPT__(__builtin_unreachable();)                                       \
    MONAD_ASSERTION_FAILED_NO_MSG(nullptr);

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
