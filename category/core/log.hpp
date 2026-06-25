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

// Project-internal logging header.  Files that emit log messages, hold a
// `quill::Logger *`, specialize `quill::DeferredFormatCodec` or
// `quill::DirectFormatCodec`, or use the `fmt::` formatter should include this
// instead of reaching directly into `<quill/...>` headers. The exception is for
// logging standard library types where the `<quill/std/...>` headers should be
// included directly.

#include <category/core/config.hpp>

#define QUILL_DISABLE_NON_PREFIXED_MACROS

#include <quill/HelperMacros.h>
#include <quill/LogMacros.h>
#include <quill/Logger.h>

#include <filesystem>
#include <type_traits>

namespace fmt = fmtquill;

// Registers `T` with quill's logging-by-copy machinery. The current
//
// Use the manual specialization form for templated types (e.g.
// `intx::uint<N>`, `monad::Delta<T>`) and for the rare non-true_type case
// (`NibblesView`) — the macro only handles the common `template <> struct
// quill::Codec<T> : quill::DeferredFormatCodec<T> {};` shape.
#define MONAD_LOG_LOGGABLE(T)                                                  \
    template <>                                                                \
    struct quill::Codec<T> : quill::DeferredFormatCodec<T>                     \
    {                                                                          \
    };

// Global root logger
extern quill::Logger *monad_root_logger;

#define LOG_DEBUG(fmt, ...)                                                    \
    QUILL_LOG_DEBUG(monad_root_logger, fmt, ##__VA_ARGS__)
#define LOG_INFO(fmt, ...) QUILL_LOG_INFO(monad_root_logger, fmt, ##__VA_ARGS__)
#define LOG_WARNING(fmt, ...)                                                  \
    QUILL_LOG_WARNING(monad_root_logger, fmt, ##__VA_ARGS__)
#define LOG_ERROR(fmt, ...)                                                    \
    QUILL_LOG_ERROR(monad_root_logger, fmt, ##__VA_ARGS__)

MONAD_NAMESPACE_BEGIN

constexpr char quill_default_pattern[] =
    "%(time) [%(thread_id)] %(file_name):%(line_number) "
    "LOG_%(log_level)\t%(message)";
constexpr char quill_default_time_format[] = "%Y-%m-%d %H:%M:%S.%Qns";

// Configures the root quill logger with the project's default pattern
// (timestamp, thread id, source location, level, message), starts the
// backend with the system signal handler installed, and sets the root
// log level. Call once near the top of main(). Not thread-safe and
// intended to only run once per process.
void init_root_logger(quill::LogLevel level);

// Starts the quill backend with the signal handler but does NOT
// configure a stdout handler. For tools and tests that don't need
// their own log output but still expect the queue to be drained.
void start_logger_minimal();

// Flushes any buffered log messages to their handlers.
void flush_logger();

// Creates a quill logger named "event_trace" backed by the given file
// with a bare "%(message)" pattern, suitable for the ENABLE_EVENT_TRACING
// path. Returns the new logger so callers can store it in
// ::monad::event_tracer (declared in
// category/execution/ethereum/trace/event_trace.hpp).
quill::Logger *create_event_tracer(std::filesystem::path const &trace_log);

MONAD_NAMESPACE_END
