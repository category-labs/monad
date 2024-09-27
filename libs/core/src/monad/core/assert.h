#pragma once

#include <monad/core/likely.h>

#ifdef __cplusplus
extern "C"
{
#endif

[[noreturn]] void monad_assertion_failed(
    char const *expr, char const *function, char const *file, long line,
    char const *msg);

#define MONAD_ASSERTION_FAILED_WITH_MSG(expr, msg)                             \
    /* Ensure msg is a static string at a fixed address; we do this because */ \
    /* MONAD_ASSERT can be used within a signal handler, and we don't want */  \
    /* a "double fault" occurring if dereferencing an unknown pointer could */ \
    /* cause a nested error, e.g., a SIGSEGV raised by reading *msg while */   \
    /* we're handling another signal */                                        \
    static_assert(__builtin_constant_p(msg));                                  \
    monad_assertion_failed(                                                    \
        #expr, __extension__ __PRETTY_FUNCTION__, __FILE__, __LINE__, msg);

/// Assert, with backtrace upon failure; accepts an optional message, which
/// must be a compile-time-constant string
#define MONAD_ASSERT(expr, ...)                                                \
    if (MONAD_LIKELY(expr)) { /* likeliest */                                  \
    }                                                                          \
    else {                                                                     \
        __VA_OPT__(MONAD_ASSERTION_FAILED_WITH_MSG(#expr, __VA_ARGS__);)       \
        __VA_OPT__(__builtin_unreachable();)                                   \
        monad_assertion_failed(                                                \
            #expr,                                                             \
            __extension__ __PRETTY_FUNCTION__,                                 \
            __FILE__,                                                          \
            __LINE__,                                                          \
            nullptr);                                                          \
    }

/// Similar to MONAD_ASSERT, but accepts a printf style message; this may not
/// be async signal safe
#define MONAD_ASSERT_PRINTF(expr, format, ...)                                 \
    if (MONAD_LIKELY(expr)) { /* likeliest */                                  \
    }                                                                          \
    else {                                                                     \
        char buf[1 << 14]; /* 16 KiB */                                        \
        char *const buf_end = buf + sizeof buf;                                \
        char *p = stpcpy(buf, "assertion failure message: ");                  \
        p += snprintf(                                                         \
            p, (size_t)(buf_end - p), (format)__VA_OPT__(, ) __VA_ARGS__);     \
        if (p < buf_end) {                                                     \
            stpncpy(p, "\n", (size_t)(buf_end - p));                           \
        }                                                                      \
        else {                                                                 \
            buf_end[-1] = '\0';                                                \
        }                                                                      \
        monad_assertion_failed(                                                \
            #expr,                                                             \
            __extension__ __PRETTY_FUNCTION__,                                 \
            __FILE__,                                                          \
            __LINE__,                                                          \
            buf);                                                              \
    }

/// Abort with a backtrace; accepts an optional message, which must be a
/// compile-time-constant string
#define MONAD_ABORT(...)                                                       \
    __VA_OPT__(MONAD_ASSERTION_FAILED_WITH_MSG(nullptr, __VA_ARGS__);)         \
    __VA_OPT__(__builtin_unreachable();)                                       \
    monad_assertion_failed(                                                    \
        nullptr,                                                               \
        __extension__ __PRETTY_FUNCTION__,                                     \
        __FILE__,                                                              \
        __LINE__,                                                              \
        nullptr);

/// Similar to MONAD_ASSERT_PRINTF, but for aborts
#define MONAD_ABORT_PRINTF(format, ...)                                        \
    {                                                                          \
        char buf[1 << 14]; /* 16 KiB */                                        \
        char *const buf_end = buf + sizeof buf;                                \
        char *p = stpcpy(buf, "abort message: ");                              \
        p += snprintf(p, buf_end - p, (format)__VA_OPT__(, ) __VA_ARGS__);     \
        if (p < buf_end) {                                                     \
            stpncpy(p, "\n", buf_end - p);                                     \
        }                                                                      \
        else {                                                                 \
            buf_end[-1] = '\0';                                                \
        }                                                                      \
        monad_assertion_failed(                                                \
            nullptr,                                                           \
            __extension__ __PRETTY_FUNCTION__,                                 \
            __FILE__,                                                          \
            __LINE__,                                                          \
            buf);                                                              \
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
