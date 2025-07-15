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
