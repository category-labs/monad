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

#include <category/core/config.hpp>
#include <category/core/log.hpp>

#include <filesystem>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr char default_pattern[] =
    "%(time) [%(thread_id)] %(file_name):%(line_number) "
    "LOG_%(log_level)\t%(message)";
constexpr char default_time_format[] = "%Y-%m-%d %H:%M:%S.%Qns";

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void init_root_logger(quill::LogLevel const level)
{
    auto const stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        default_pattern, default_time_format, quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(cfg);
    quill::start(true);
    quill::get_root_logger()->set_log_level(level);
}

void start_logger_minimal()
{
    quill::start(true);
}

void flush_logger()
{
    quill::flush();
}

quill::Logger *create_event_tracer(std::filesystem::path const &trace_log)
{
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    return quill::create_logger(
        "event_trace", quill::file_handler(trace_log, handler_cfg));
}

MONAD_NAMESPACE_END
