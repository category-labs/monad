#include <monad/core/assert.h>

#include <stdio.h>
#include <stdlib.h>

void monad_assertion_failed(
    char const *const expr, char const *const function, char const *const file,
    long const line)
{
    fprintf(
        stderr,
        "%s:%ld: %s: Assertion '%s' failed.\n",
        file,
        line,
        function,
        expr);
    fflush(stderr);
    abort();
}
