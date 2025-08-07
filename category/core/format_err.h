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

#pragma once

/**
 * @file
 *
 * This file defines two utility functions for C APIs that need a simple error
 * reporting strategy with no dependencies. The strategy is used for the
 * `monad_event_` API because it is shared as an external library, but this
 * strategy can be reused by any small C API. The strategy is:
 *
 *   - All functions that can fail return an int, and the int is an errno(3)
 *     domain error code
 *
 *   - All errors should produce a human-readable explanation; a helper macro
 *     captures the source code location
 *
 *   - Your API defines a function that returns the explanation string for the
 *     last error that occurred on that thread, e.g.,
 *     calling `monad_event_get_last_error` will give the string explanation
 *     for the last non-zero errno code on the thread
 *
 *  To reuse this utility, create a fixed size thread local buffer to hold
 *  the string explanation, a "get last error" function that returns that
 *  buffer, and a helper macro. The helper macro captures the source location
 *  and bakes in the variable name of that API's thread local error buffer. A
 *  brief example for a hypothetical "my-api":
 *
 *  my-api.c:
 *
 *     #include <category/core/format_err.h>
 *     #include <category/core/srcloc.h>
 *
 *     static thread_local g_my_api_err[1024];
 *
 *     char const *my_api_get_last_error() {
 *         return g_my_api_err;
 *     }
 *
 *     #define FORMAT_ERR(...)                                           \
 *     monad_format_err(g_my_api_err, sizeof(g_my_api_err),              \
 *                      &MONAD_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)
 *
 *  Example usage:
 *
 *     int my_api_open_file(char const *path) {
 *         int fd = open(path, O_RDWR);
 *         if (fd == -1) {
 *             return FORMAT_ERR(errno, "open of `%s` failed", path);
 *         }
 *         return 0;
 *     }
 *
 *     assert(my_api_open_file("/oh_no") == ENOENT);
 *     assert(strcmp(my_api_get_last_error(), "open of `/oh_no` failed") == 0);
 */

#include <stdarg.h>
#include <stddef.h>

#include <category/core/srcloc.h>

#ifdef __cplusplus
extern "C"
{
#endif

int monad_vformat_err(
    char *err_buf, size_t err_buf_size, monad_source_location_t const *,
    int err, char const *format, va_list ap);

__attribute__((format(printf, 5, 6))) static inline int monad_format_err(
    char *err_buf, size_t err_buf_size, monad_source_location_t const *src,
    int err, char const *format, ...)
{
    va_list ap;
    int rc;
    va_start(ap, format);
    rc = monad_vformat_err(err_buf, err_buf_size, src, err, format, ap);
    va_end(ap);
    return rc;
}

#ifdef __cplusplus
} // extern "C"
#endif
