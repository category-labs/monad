#pragma once

#include "boost_result.h"

#include <stdio.h>
#include <stdlib.h>

#ifndef __clang__
    #if defined(__SANITIZE_ADDRESS__)
        #define MONAD_HAVE_ASAN 1
    #elif defined(__SANITIZE_THREAD__)
        #define MONAD_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_HAVE_UBSAN 1
    #endif
#else
    #if __has_feature(address_sanitizer)
        #define MONAD_HAVE_ASAN 1
    #elif __has_feature(thread_sanitizer)
        #define MONAD_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_HAVE_UBSAN 1
    #endif
#endif

#ifndef MONAD_CPP_STD
    #ifdef __cplusplus
        #define MONAD_CPP_STD std::
    #else
        #define MONAD_CPP_STD
    #endif
#endif

#ifndef MONAD_CPP_ATOMIC
    #ifdef __cplusplus
        #define MONAD_CPP_ATOMIC(x) std::atomic<x>
    #else
        #define MONAD_CPP_ATOMIC(x) x _Atomic
    #endif
#endif

//! \brief Declare a Boost.Outcome layout compatible C result type for
//! `result<intptr_t>`
BOOST_OUTCOME_C_DECLARE_RESULT_SYSTEM(monad, intptr_t)

#define MONAD_CHECK_RESULT2(unique, ...)                                       \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) {                        \
            fprintf(                                                           \
                stderr,                                                        \
                "FATAL: %s\n",                                                 \
                outcome_status_code_message(&unique.error));                   \
            abort();                                                           \
        }                                                                      \
    }
#define MONAD_CHECK_RESULT(...)                                                \
    MONAD_CHECK_RESULT2(BOOST_OUTCOME_TRY_UNIQUE_NAME, __VA_ARGS__)

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Convenience typedef
typedef BOOST_OUTCOME_C_RESULT_SYSTEM(monad) monad_c_result;

//! \brief Return a successful `monad_c_result` for a given `intptr_t`
BOOST_OUTCOME_C_NODISCARD extern BOOST_OUTCOME_C_WEAK monad_c_result
monad_c_make_success(intptr_t v)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_SUCCESS(monad, v);
}

//! \brief Return a failure `monad_c_result` for a given `errno`
BOOST_OUTCOME_C_NODISCARD extern BOOST_OUTCOME_C_WEAK monad_c_result
monad_c_make_failure(int ec)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_FAILURE_SYSTEM(monad, ec);
}

#ifdef __cplusplus
}
#endif
