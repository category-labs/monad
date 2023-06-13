#pragma once

#include <monad/logging/config.hpp>

#include <memory>
#include <optional>
#include <string>

MONAD_LOG_NAMESPACE_BEGIN

enum class FakeLogLevel : uint8_t
{
    TraceL3,
    TraceL2,
    TraceL1,
    Debug,
    Info,
    Warning,
    Error,
    Critical,
    Backtrace,
    None
};

struct FakeEmptyLogger
{
    static constexpr void start() noexcept {}

    static constexpr void *get_logger(char const * = nullptr) noexcept
    {
        return nullptr;
    }

    static constexpr void *create_logger(std::string const &) noexcept
    {
        return nullptr;
    }

    static constexpr void set_log_level(
        char const * = nullptr, FakeLogLevel = FakeLogLevel::Info) noexcept
    {
        return;
    }
};

MONAD_LOG_NAMESPACE_END
