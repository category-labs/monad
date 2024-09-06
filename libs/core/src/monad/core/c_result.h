#pragma once

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>

#include <monad/core/likely.h>

/// Return value of most monad C functions that can fail; this type can
/// interoperate with the Boost.Outcome C++ library, and is layout compatible
/// with the `status_result<intptr_t>` type from that library
typedef struct monad_status_result monad_c_result;

/// Represents a (category, numerical_code) error pair, similar to in concept
/// to C++11 std::error_code but `domain` points to Boost.Outcome machinery
/// instead of a std::error_category
struct monad_error_code
{
    void *domain;
    intptr_t value;
};

struct monad_status_result
{
    intptr_t value;
    unsigned flags;
    struct monad_error_code error;
};

#define MONAD_RESULT_FLAG_VALUE 0x1
#define MONAD_RESULT_FLAG_ERROR 0x2

static inline bool monad_result_has_value(monad_c_result mcr)
{
   return (mcr.flags & MONAD_RESULT_FLAG_VALUE) == MONAD_RESULT_FLAG_VALUE;
}

static inline bool monad_result_has_error(monad_c_result mcr)
{
    return (mcr.flags & MONAD_RESULT_FLAG_ERROR) == MONAD_RESULT_FLAG_ERROR;
}

#define MONAD_OK(X) MONAD_LIKELY(monad_result_has_value(X))
#define MONAD_FAILED(X) MONAD_UNLIKELY(monad_result_has_error(X))

#define MONAD_BOOST_RESULT_INCLUDE_OK
#include "boost_result.h"
#undef MONAD_BOOST_RESULT_INCLUDE_OK

static inline monad_c_result monad_c_make_success(intptr_t value)
{
    #ifdef __cplusplus
    return {value, MONAD_RESULT_FLAG_VALUE, {}};
    #else
    return (monad_c_result){value, MONAD_RESULT_FLAG_VALUE, (struct monad_error_code){nullptr, 0}};
    #endif
}

static inline monad_c_result monad_c_make_failure(intptr_t errcode)
{
    struct monad_status_result ret;
    outcome_make_result_status_code_failure_system(
        (void *)&ret,
        sizeof(ret),
        offsetof(struct monad_status_result, flags),
        errcode);
    return ret;
}

/// Similar to the BSD utility function verrc(3) from <err.h>, but taking
/// a `struct monad_error_code` instead of an errno(3) integer code
#ifdef __cplusplus
extern "C"
#endif
[[noreturn]] void monad_verrc(
    int eval, struct monad_error_code code, char const *format, va_list ap);

/// Variadic form of monad_verrc
[[noreturn]] static inline void
monad_errc(int eval, struct monad_error_code code, char const *format, ...)
{
    va_list ap;
    va_start(ap, format);
    monad_verrc(eval, code, format, ap);
    va_end(ap);
}
