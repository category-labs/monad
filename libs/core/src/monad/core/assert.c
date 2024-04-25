#include <monad/core/assert.h>

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

extern char const *__progname;

extern void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    _Bool print_async_unsafe_info);

void monad_assertion_failed(
    char const *const expr, char const *const function, char const *const file,
    long const line)
{
    // This NEEDS to remain async signal safe!
    char buffer[16384];
    monad_stack_backtrace_capture_and_print(buffer, sizeof(buffer), 2, 3, 1);
    ssize_t written = snprintf(
        buffer,
        sizeof(buffer),
        "%s: %s:%ld: %s: Assertion '%s' failed.\n",
        __progname,
        file,
        line,
        function,
        expr);
    if ((size_t)written >= sizeof(buffer)) {
        written = (int)(sizeof(buffer) - 1);
    }
    // abort() is async signal safe in glibc
    written = write(2 /*stderr*/, buffer, (size_t)written);
    if (written == -1) {
        // This is to shut up the warning
        abort();
    }
    abort();
}
