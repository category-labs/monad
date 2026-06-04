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

#pragma once

#include <category/core/config.hpp>

#include <format>

namespace fmt = std;

#define MONAD_LOG_LOGGABLE(T)

namespace quill
{
    // Forward-declared for int_fmt.hpp, state_deltas_fmt.hpp,
    // nibbles_view_fmt.hpp which hand-write `template <> struct
    // quill::copy_loggable<T> : std::true_type
    template <class>
    struct copy_loggable;

    // event_trace.hpp declares `extern quill::Logger *event_tracer;` and
    // event_trace.cpp defines it as nullptr, so a forward-declare here is
    // sufficient
    class Logger;
}

#define LOG_INFO(...)
#define LOG_WARNING(...)
#define LOG_ERROR(...)
#define LOG_DEBUG(...)
#define LOG_TRACE_L1(...)
#define LOG_TRACE_L2(...)
#define LOG_TRACE_L3(...)
#define LOG_CRITICAL(...)
#define QUILL_LOG_INFO(...)
#define QUILL_LOG_WARNING(...)
#define QUILL_LOG_ERROR(...)
#define QUILL_LOG_DEBUG(...)
