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

#include <quill/Backend.h>
#include <quill/Frontend.h>
#include <quill/sinks/ConsoleSink.h>
#include <quill/sinks/FileSink.h>
#include <quill/sinks/NullSink.h>

#include <filesystem>
#include <utility>

quill::Logger *monad_root_logger;

MONAD_NAMESPACE_BEGIN

void init_root_logger(quill::LogLevel const level)
{
    monad_root_logger = quill::Frontend::create_or_get_logger(
        "root",
        quill::Frontend::create_or_get_sink<quill::ConsoleSink>("root_sink"),
        quill::PatternFormatterOptions{
            quill_default_pattern,
            quill_default_time_format,
            quill::Timezone::GmtTime});
    monad_root_logger->set_log_level(level);
    quill::Backend::start();
}

void start_logger_minimal()
{
    monad_root_logger = quill::Frontend::create_or_get_logger(
        "root",
        quill::Frontend::create_or_get_sink<quill::NullSink>("null_sink"));
    quill::Backend::start();
}

void flush_logger()
{
    monad_root_logger->flush_log();
}

quill::Logger *create_event_tracer(std::filesystem::path const &trace_log)
{
    auto file_sink =
        quill::Frontend::create_or_get_sink<quill::FileSink>(trace_log);

    return quill::Frontend::create_or_get_logger(
        "event_trace",
        std::move(file_sink),
        quill::PatternFormatterOptions{"%(message)", ""});
}

MONAD_NAMESPACE_END
