#pragma once

/**
 * @file
 *
 * The error reporting strategies of event_recorder.h and event_server.h are
 * similar and share a utility function defined here.
 */

#include <stdarg.h>
#include <stddef.h>

typedef struct monad_source_location monad_source_location_t;

int _monad_event_vformat_err(
    char *error_buf, size_t size, monad_source_location_t const *srcloc,
    int err, char const *format, va_list ap);
