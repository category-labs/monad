#pragma once

/**
 * @file
 *
 * The error reporting strategies of event.c, event_test_util.c, and
 * event_recorder.c (in the writer) are similar and share the utility functions
 * defined here.
 */

#include <stdarg.h>
#include <stddef.h>

// A pure C structure similar to C++20's std::source_location
struct monad_event_source_location
{
    char const *function_name;
    char const *file_name;
    unsigned line;
    unsigned column;
};

#define MONAD_EVENT_SOURCE_LOCATION_CURRENT()                                  \
    ((struct monad_event_source_location){                                     \
        __PRETTY_FUNCTION__, __FILE__, __LINE__, 0})

int _monad_event_vformat_err(
    char *err_buf, size_t err_buf_size,
    struct monad_event_source_location const *, int err, char const *format,
    va_list ap);

static inline int _monad_event_format_err(
    char *err_buf, size_t err_buf_size,
    struct monad_event_source_location const *src, int err, char const *format,
    ...)
{
    va_list ap;
    int rc;
    va_start(ap, format);
    rc = _monad_event_vformat_err(err_buf, err_buf_size, src, err, format, ap);
    va_end(ap);
    return rc;
}
