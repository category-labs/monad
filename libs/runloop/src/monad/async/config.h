#pragma once

#include "boost_result.h"

#ifndef __clang__
    #if defined(__SANITIZE_ADDRESS__)
        #define MONAD_ASYNC_HAVE_ASAN 1
    #elif defined(__SANITIZE_THREAD__)
        #define MONAD_ASYNC_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_ASYNC_HAVE_UBSAN 1
    #endif
#else
    #if __has_feature(address_sanitizer)
        #define MONAD_ASYNC_HAVE_ASAN 1
    #elif __has_feature(thread_sanitizer)
        #define MONAD_ASYNC_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_ASYNC_HAVE_UBSAN 1
    #endif
#endif

#ifndef MONAD_ASYNC_NODISCARD
    #if defined __STDC_VERSION__ && __STDC_VERSION__ >= 202000L
        #define MONAD_ASYNC_NODISCARD [[nodiscard]]
    #else
        #define MONAD_ASYNC_NODISCARD __attribute__((warn_unused_result))
    #endif
#endif

#ifndef MONAD_ASYNC_PUBLIC_CONST
    #ifdef MONAD_ASYNC_SOURCE
        #define MONAD_ASYNC_PUBLIC_CONST
    #else
        #define MONAD_ASYNC_PUBLIC_CONST const
    #endif
#endif

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Declare a Boost.Outcome layout compatible C result type for
//! `result<intptr_t>`
BOOST_OUTCOME_C_DECLARE_RESULT_SYSTEM(monad_async, intptr_t);

//! \brief Convenience typedef
typedef BOOST_OUTCOME_C_RESULT_SYSTEM(monad_async) monad_async_result;

//! \brief Return a successful `monad_async_result` for a given `intptr_t`
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_make_success(intptr_t v);
//! \brief Return a failure `monad_async_result` for a given `errno`
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_make_failure(int ec);

//! \brief A type representing the tick count on the CPU
typedef uint64_t monad_async_cpu_ticks_count_t;

#define MONAD_ASYNC_GLUE2(x, y) x##y
#define MONAD_ASYNC_GLUE(x, y) MONAD_ASYNC_GLUE2(x, y)
#define MONAD_ASYNC_UNIQUE_NAME                                                \
    MONAD_ASYNC_GLUE(_monad_async_unique_name_temporary, __COUNTER__)

#define MONAD_ASYNC_CHECK_RESULT2(unique, ...)                                 \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) {                        \
            if (BOOST_OUTCOME_C_RESULT_ERROR_IS_ERRNO(unique)) {               \
                fprintf(                                                       \
                    stderr, "FATAL: %s\n", strerror((int)unique.error.value)); \
                abort();                                                       \
            }                                                                  \
            else {                                                             \
                fprintf(                                                       \
                    stderr,                                                    \
                    "FATAL: Failure value = %d domain = %p\n",                 \
                    (int)unique.error.value,                                   \
                    unique.error.domain);                                      \
                abort();                                                       \
            }                                                                  \
        }                                                                      \
    }

//! \brief Check a result for failure and abort if so with diagnostic
#define MONAD_ASYNC_CHECK_RESULT(...)                                          \
    MONAD_ASYNC_CHECK_RESULT2(MONAD_ASYNC_UNIQUE_NAME, __VA_ARGS__)

#define MONAD_ASYNC_TRY_RESULT2(unique, cleanup, ...)                          \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) {                        \
            cleanup;                                                           \
            return unique;                                                     \
        }                                                                      \
    }
//! \brief Check a result for failure and propagate upwards
#define MONAD_ASYNC_TRY_RESULT(cleanup, ...)                                   \
    MONAD_ASYNC_TRY_RESULT2(MONAD_ASYNC_UNIQUE_NAME, cleanup, __VA_ARGS__)

//! \brief Task priority classes
typedef enum monad_async_priority
    : unsigned char
{
    monad_async_priority_high = 0,
    monad_async_priority_normal = 1,
    monad_async_priority_low = 2,

    monad_async_priority_max = 3,
    monad_async_priority_unchanged = (unsigned char)-1
} monad_async_priority;
#ifdef __cplusplus
}
#endif
