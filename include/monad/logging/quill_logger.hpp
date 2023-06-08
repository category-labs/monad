#pragma once

#include <monad/logging/config.hpp>
#include <monad/logging/formatter.hpp>

#include <memory>
#include <optional>
#include <string>

#include <quill/Quill.h>

MONAD_LOG_NAMESPACE_BEGIN

struct QuillLogger
{
    static void start() { quill::start(); }

    [[nodiscard]] static quill::Logger *
    get_logger(char const *logger_name = nullptr)
    {
        return quill::get_logger(logger_name);
    }

    [[nodiscard]] static quill::Logger *create_logger(
        std::string const &logger_name,
        std::optional<quill::TimestampClockType> timestamp_clock_type =
            std::nullopt,
        std::optional<quill::TimestampClock *> timestamp_clock = std::nullopt)
    {
        return quill::create_logger(
            logger_name, timestamp_clock_type, timestamp_clock);
    }

    [[nodiscard]] static quill::Logger *create_logger(
        std::string const &logger_name,
        std::shared_ptr<quill::Handler> &&handler,
        std::optional<quill::TimestampClockType> timestamp_clock_type =
            std::nullopt,
        std::optional<quill::TimestampClock *> timestamp_clock = std::nullopt)
    {
        return quill::create_logger(
            logger_name,
            std::move(handler),
            timestamp_clock_type,
            timestamp_clock);
    }

    static void set_log_level(
        char const *logger_name = nullptr,
        quill::LogLevel log_level = quill::LogLevel::Info)
    {
        auto logger = get_logger(logger_name);
        logger->set_log_level(log_level);
    }
};

MONAD_LOG_NAMESPACE_END