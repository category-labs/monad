#include <monad/core/assert.h>

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

extern char const *__progname;

extern void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info);

void monad_assertion_failed_vprintf(
    char const *const expr, char const *const function, char const *const file,
    long const line, char const *format, va_list ap)
{
    // This NEEDS to remain async signal safe!
    char buffer[16384];
    ssize_t written;
    monad_stack_backtrace_capture_and_print(
        buffer, sizeof(buffer), STDERR_FILENO, 3, true);
    if (expr != nullptr) {
        written = snprintf(
            buffer,
            sizeof(buffer),
            "%s: %s:%ld: %s: Assertion '%s' failed.\n",
            __progname,
            file,
            line,
            function,
            expr);
    }
    else {
        // expr == nullptr is an abort
        written = snprintf(
            buffer,
            sizeof(buffer),
            "%s: %s:%ld: %s: MONAD_ABORT called.\n",
            __progname,
            file,
            line,
            function);
    }
    if ((size_t)written >= sizeof(buffer)) {
        written = (int)(sizeof(buffer) - 1);
    }
    if (format != nullptr && written < (int)(sizeof buffer - 1)) {
        written += vsnprintf(
            buffer + written, sizeof buffer - (size_t)written, format, ap);
        if ((size_t)written >= sizeof(buffer)) {
            written = (int)(sizeof(buffer) - 1);
        }
        else {
            buffer[written++] = '\n';
        }
    }
    // abort() is async signal safe in glibc
    written = write(2 /*stderr*/, buffer, (size_t)written);
    if (written == -1) {
        // This is to shut up the warning
        abort();
    }
    abort();
}
