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

#include <category/execution/ethereum/trace/event_trace.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

namespace fmt = fmtquill::v10;

template <>
struct quill::copy_loggable<monad::TraceEvent> : std::true_type
{
};

template <>
struct fmt::formatter<monad::TraceEvent> : public fmt::ostream_formatter
{
};
