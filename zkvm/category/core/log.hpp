// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM shadow of category/core/log.hpp. The host's log.hpp pulls in quill,
// which needs a runtime backend thread and threading primitives — both
// unavailable on bare-metal RISC-V. We collapse LOG_* macros to discard
// expressions so the call sites still parse, and alias `fmt` onto std::
// so existing `fmt::format` / `struct fmt::formatter<T>` specializations
// keep working through libstdc++'s std::format (GCC 13+).

#pragma once

#include <category/core/config.hpp>

#include <format>

namespace fmt = std;

// Specializations of MONAD_LOG_LOGGABLE(T) attach a quill copy_loggable
// trait so quill knows how to ship T across to its backend. The shadow
// never logs, so the macro expands to nothing — call sites at namespace
// scope still parse because the trailing semicolon they pair it with is
// stand-alone-legal in C++17+.
#define MONAD_LOG_LOGGABLE(T)

// A few headers (int_fmt.hpp, state_deltas_fmt.hpp, nibbles_view_fmt.hpp)
// hand-write `template <> struct quill::copy_loggable<T> : std::true_type
// {};` instead of using MONAD_LOG_LOGGABLE. Forward-declare the primary
// so those specializations parse without dragging in <quill/Quill.h>.
namespace quill
{
    template <class>
    struct copy_loggable;

    // event_trace.hpp declares `extern quill::Logger *event_tracer;` and
    // event_trace.cpp defines it as nullptr. Quill 12's real Logger is an
    // alias needing <quill/Logger.h>; the shadow drops quill entirely, so
    // forward-declare an incomplete type — it is only ever used as a pointer.
    class Logger;
}

// Log-level macros: cast each argument to void so unused-variable warnings
// stay quiet and side-effecting expressions still evaluate. Doing it as a
// fold-expression keeps a trailing semicolon mandatory at the call site.
#define MONAD_ZKVM_LOG_DISCARD(...)                                            \
    do {                                                                       \
        (void)sizeof(((__VA_ARGS__), 0));                                      \
    }                                                                          \
    while (0)

#define LOG_INFO(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_WARNING(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_ERROR(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_DEBUG(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_TRACE_L1(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_TRACE_L2(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_TRACE_L3(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define LOG_CRITICAL(...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define QUILL_LOG_INFO(logger, ...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define QUILL_LOG_WARNING(logger, ...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define QUILL_LOG_ERROR(logger, ...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
#define QUILL_LOG_DEBUG(logger, ...) MONAD_ZKVM_LOG_DISCARD(__VA_ARGS__)
