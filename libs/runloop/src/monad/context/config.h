#pragma once

#include <stdint.h>

#ifndef __clang__
    #if defined(__SANITIZE_ADDRESS__)
        #define MONAD_CONTEXT_HAVE_ASAN 1
    #elif defined(__SANITIZE_THREAD__)
        #define MONAD_CONTEXT_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_CONTEXT_HAVE_UBSAN 1
    #endif
#else
    #if __has_feature(address_sanitizer)
        #define MONAD_CONTEXT_HAVE_ASAN 1
    #elif __has_feature(thread_sanitizer)
        #define MONAD_CONTEXT_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_CONTEXT_HAVE_UBSAN 1
    #endif
#endif

#ifndef MONAD_CONTEXT_PUBLIC_CONST
    #if defined(MONAD_ASYNC_SOURCE) || defined(MONAD_CONTEXT_SOURCE)
        #define MONAD_CONTEXT_PUBLIC_CONST
    #else
        #define MONAD_CONTEXT_PUBLIC_CONST const
    #endif
#endif

#ifndef MONAD_CONTEXT_CPP_STD
    #ifdef __cplusplus
        #define MONAD_CONTEXT_CPP_STD std::
    #else
        #define MONAD_CONTEXT_CPP_STD
    #endif
#endif

#ifndef MONAD_CONTEXT_ATOMIC
    #ifdef __cplusplus
        #define MONAD_CONTEXT_ATOMIC(x) std::atomic<x>
    #else
        #define MONAD_CONTEXT_ATOMIC(x) x _Atomic
    #endif
#endif

#include <monad/core/c_result.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief A type representing the tick count on the CPU
typedef uint64_t monad_context_cpu_ticks_count_t;

#define MONAD_CONTEXT_CHECK_RESULT2(unique, ...)                               \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (MONAD_FAILED(unique)) {                                            \
            fprintf(                                                           \
                stderr,                                                        \
                "FATAL: %s\n",                                                 \
                outcome_status_code_message(&unique.error));                   \
            abort();                                                           \
        }                                                                      \
    }
#define MONAD_CONTEXT_CHECK_RESULT(...)                                        \
    MONAD_CONTEXT_CHECK_RESULT2(BOOST_OUTCOME_TRY_UNIQUE_NAME, __VA_ARGS__)

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
