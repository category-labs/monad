// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/assert.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>

extern char const *__progname; // NOLINT(bugprone-reserved-identifier)

extern void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info);

void monad_assertion_failed(
    char const *const expr, char const *const function, char const *const file,
    long const line, char const *msg)
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
    if (written < 0 || (size_t)written >= sizeof(buffer)) {
        written = (ssize_t)sizeof(buffer) - 1;
    }
    if (msg != nullptr) {
        written += (ssize_t)strlcpy(
            buffer + written, msg, sizeof(buffer) - (size_t)written);
        if ((size_t)written >= sizeof(buffer)) {
            written = (int)(sizeof(buffer) - 1);
        }
        else {
            buffer[written++] = '\n';
        }
    }
    // abort() is async signal safe in glibc
    if (write(STDERR_FILENO, buffer, (size_t)written) == -1) {
        abort(); // Needed because of -Werror=unused-result
    }
    abort();
}
