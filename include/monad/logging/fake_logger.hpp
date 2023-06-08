#pragma once

#include <monad/logging/config.hpp>

#include <memory>
#include <optional>
#include <string>

MONAD_LOG_NAMESPACE_BEGIN

enum class FakeLogLevel : uint8_t
{
    FakeTraceL3,
    FakeTraceL2,
    FakeTraceL1,
    FakeDebug,
    FakeInfo,
    FakeWarning,
    FakeError,
    FakeCritical,
    FakeBacktrace,
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
        char const * = nullptr, FakeLogLevel = FakeLogLevel::FakeInfo) noexcept
    {
        return;
    }
};

MONAD_LOG_NAMESPACE_END