#pragma once

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>

#include <monad/core/boost_result.h>
#include <monad/core/likely.h>

/// The return type of many monad C functions that can fail; this type
/// interoperates with the Boost.Outcome C++ library; it is layout compatible
/// with the `status_result<intptr_t>` type from that library
typedef BOOST_OUTCOME_C_RESULT_SYSTEM(monad) monad_c_result;

/// Provides the complete type definition for `monad_c_result` (which is
/// otherwise incomplete) and the various inline functions that form its
/// public interface
BOOST_OUTCOME_C_DECLARE_RESULT_SYSTEM(monad, intptr_t)

/// Returns true if the result was successful; in this case the field
/// `intptr_t monad_c_result::value` will contain a value
[[gnu::always_inline]] static inline bool
monad_result_has_value(monad_c_result r)
{
    return BOOST_OUTCOME_C_RESULT_HAS_VALUE(r);
}

/// Returns true if the result contains an error; in this case the field
/// `struct cxx_status_code_system monad_c_result::error` will contain an error
/// object
[[gnu::always_inline]] static inline bool
monad_result_has_error(monad_c_result r)
{
    return BOOST_OUTCOME_C_RESULT_HAS_ERROR(r);
}

#define MONAD_OK(X) MONAD_LIKELY(monad_result_has_value(X))

#define MONAD_FAILED(X) MONAD_UNLIKELY(monad_result_has_error(X))

/// Return a successful `monad_c_result` for a given `intptr_t`
static inline monad_c_result monad_c_make_success(intptr_t value)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_SUCCESS(monad, value);
}

/// Return a failure `monad_c_result` with the given `errno` domain code
static inline monad_c_result monad_c_make_failure(intptr_t ec)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_FAILURE_SYSTEM(monad, ec);
}

/// Similar to the BSD utility function verrc(3) from <err.h>, but taking
/// a `struct cxx_status_code_system` instead of an errno(3) integer code;
/// this is the type of the `monad_c_result::error` field
#ifdef __cplusplus
extern "C"
#endif
[[noreturn]] void monad_verrc(
    int eval, struct cxx_status_code_system err_code, char const *format, va_list ap);

/// Variadic form of monad_verrc
[[noreturn]] static inline void monad_errc(
    int eval, struct cxx_status_code_system err_code, char const *format, ...)
{
    va_list ap;
    va_start(ap, format);
    monad_verrc(eval, err_code, format, ap);
    va_end(ap);
}

#ifdef __cplusplus

[[nodiscard, gnu::always_inline]] inline monad_c_result to_monad_c_result(
    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<intptr_t> v)
{
    return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, std::move(v));
}

#endif
