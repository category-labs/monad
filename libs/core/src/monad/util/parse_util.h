#pragma once

#include <monad/core/c_result.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_strtonum_error
{
    MONAD_STN_INVALID = 0,
    MONAD_STN_BAD_RANGE = 1,
    MONAD_STN_NOT_INT_TOKEN = 2,
    MONAD_STN_TOO_SMALL = 3,
    MONAD_STN_TOO_BIG = 4
};

/// A port of the OpenBSD strtonum(3) utility, except returning a
/// @ref monad_c_result
monad_c_result
monad_strtonum(char const *nptr, intptr_t min_val, intptr_t max_val);

bool outcome_status_code_equal_strtonum_error(
    struct monad_error_code, enum monad_strtonum_error);

#ifdef __cplusplus
}
#endif
