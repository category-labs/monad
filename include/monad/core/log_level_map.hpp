#pragma once

#include <monad/config.hpp>

#include <quill/LogLevel.h>

#include <string>
#include <unordered_map>

MONAD_NAMESPACE_BEGIN

inline std::unordered_map<std::string, quill::LogLevel> const log_level_map = {
    {"tracel3", quill::LogLevel::TraceL3},
    {"trace_l3", quill::LogLevel::TraceL3},
    {"tracel2", quill::LogLevel::TraceL2},
    {"trace_l2", quill::LogLevel::TraceL2},
    {"tracel1", quill::LogLevel::TraceL1},
    {"trace_l1", quill::LogLevel::TraceL1},
    {"debug", quill::LogLevel::Debug},
    {"info", quill::LogLevel::Info},
    {"warning", quill::LogLevel::Warning},
    {"error", quill::LogLevel::Error},
    {"critical", quill::LogLevel::Critical},
    {"none", quill::LogLevel::None}};

MONAD_NAMESPACE_END
