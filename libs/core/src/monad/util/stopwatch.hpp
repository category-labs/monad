#pragma once

#include <monad/config.hpp>

#include <quill/Quill.h>

#include <chrono>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

template <typename Duration = std::chrono::nanoseconds>
class Stopwatch final
{
    char const *const name_;
    int64_t const min_;
    std::chrono::time_point<std::chrono::steady_clock> const begin_;

public:
    Stopwatch(char const *const name, int64_t const min = 0)
        : name_{name}
        , min_{min}
        , begin_{std::chrono::steady_clock::now()}
    {
    }

    ~Stopwatch()
    {
        auto const end = std::chrono::steady_clock::now();
        auto const duration =
            std::chrono::duration_cast<Duration>(end - begin_);
        if (duration.count() >= min_) {
            LOG_INFO("{} {}", name_, duration);
        }
    }
};

MONAD_NAMESPACE_END
