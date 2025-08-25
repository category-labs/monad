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
 * This file defines an interface to initialize the logging framework and
 * consume log messages, when `libmonad_execution` is hosted inside of a
 * non-C++ language environment.
 *
 * In an ordinary C++ program, the logging system can be directly configured
 * using a C++ API. When outside of C++, this C API can be used via the host
 * language's C FFI facility. It provides a function to initialize the logging
 * system and the ability to plumb log messages into the host's environment
 * using callback functions.
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Object passed to external consumers of log messages
struct monad_log
{
    uint8_t syslog_level;
    char const *message;
    size_t message_len;
};

/// Opaque object representing a log handler (a subscriber / observer of logs)
struct monad_log_handler;

/// Signature of consumer callback that writes log messages
typedef void(monad_log_write_callback)(
    struct monad_log const *, uintptr_t user);

/// Signature of consumer callback that flushes the writer's stream, if
/// applicable
typedef void(monad_log_flush_callback)(uintptr_t user);

/// Create a callback-based handler for logs; when a log message is generated,
/// it will be packaged in a `struct monad_log` object and passed to the write
/// callback
int monad_log_handler_create(
    struct monad_log_handler **, char const *name, monad_log_write_callback *,
    monad_log_flush_callback *, uintptr_t user);

/// Create a log handler that writes to stdout
int monad_log_handler_create_stdout_handler(struct monad_log_handler **);

/// Destroy a previously created log handler
void monad_log_handler_destroy(struct monad_log_handler *);

/// Initialize the logging system with the provided array of handlers, and
/// filtering with the provided log level; the log level is taken from syslog(3)
/// with tracing extensions (i.e., LOG_DEBUG + 1 is the first trace level)
int monad_log_init(
    struct monad_log_handler **, size_t handler_count, uint8_t syslog_level);

/// Return a string description of the last error that occurred on this thread
char const *monad_log_get_last_error();

#ifdef __cplusplus
} // extern "C"
#endif
