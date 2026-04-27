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

// Project-internal logging header — the single chokepoint for everything
// the codebase pulls from quill. Files that emit log messages, hold a
// `quill::Logger *`, specialize `quill::copy_loggable`, or use the `fmt::`
// formatter should include this instead of reaching directly into
// `<quill/...>` headers.
//
// Today this re-exports `<quill/Quill.h>`, which transitively provides
// every quill name our code uses (LogLevel, Logger, Handler, FileHandler,
// the bundled `fmtquill` formatter, etc.). The `fmt` alias points at
// `fmtquill` rather than `fmtquill::v10` so it survives the inline-namespace
// tag bump (v10 → v12) in the upcoming quill v11 upgrade — call sites that
// say `fmt::format(...)` keep working without source changes.
//
// The upcoming quill v11 upgrade splits the umbrella across
// Backend/Frontend/LogMacros and removes the QUILL_ROOT_LOGGER_ONLY mode;
// at that point this file becomes where the wrapper macros and
// `quill::get_root_logger()` shim live, so call sites don't need to change
// again.

#include <category/core/config.hpp>

#include <quill/Quill.h>

#include <filesystem>
#include <type_traits>

namespace fmt = fmtquill;

// Registers `T` with quill's logging-by-copy machinery. The current
// implementation specializes `quill::copy_loggable<T>`; the upcoming v11
// upgrade replaces that with `quill::Codec<T> : DirectFormatCodec<T>`, so
// every site that uses this macro picks up the new shape with no edit.
//
// Use the manual specialization form for templated types (e.g.
// `intx::uint<N>`, `monad::Delta<T>`) and for the rare non-true_type case
// (`NibblesView`) — the macro only handles the common
// `template <> struct quill::copy_loggable<T> : std::true_type {};` shape.
#define MONAD_LOG_LOGGABLE(T)                                                  \
    template <>                                                                \
    struct quill::copy_loggable<T> : std::true_type                            \
    {                                                                          \
    }

MONAD_NAMESPACE_BEGIN

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
