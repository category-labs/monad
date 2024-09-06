#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>

#include <monad/core/c_result.h>
#include <monad/util/parse_util.h>

extern monad_c_result monad_strtonum_make_failure(enum monad_strtonum_error);

monad_c_result
monad_strtonum(char const *nptr, intptr_t min_val, intptr_t max_val)
{
    intptr_t value;
    char *nptr_end;
    if (nptr == nullptr) {
        return monad_c_make_failure(EFAULT);
    }
    if (min_val > max_val) {
        return monad_strtonum_make_failure(MONAD_STN_BAD_RANGE);
    }
    value = strtoll(nptr, &nptr_end, 10);
    if (nptr == nptr_end || *nptr_end != '\0') {
        return monad_strtonum_make_failure(MONAD_STN_NOT_INT_TOKEN);
    }
    if ((value == LLONG_MIN && errno == ERANGE) || value < min_val) {
        return monad_strtonum_make_failure(MONAD_STN_TOO_SMALL);
    }
    if ((value == LLONG_MAX && errno == ERANGE) || value > max_val) {
        return monad_strtonum_make_failure(MONAD_STN_TOO_BIG);
    }
    return monad_c_make_success(value);
}
