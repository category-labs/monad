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

#include <category/core/config.hpp>

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
    bool ignore_result_{false};

public:
    Stopwatch(char const *const name, int64_t const min = 0)
        : name_{name}
        , min_{min}
        , begin_{std::chrono::steady_clock::now()}
    {
    }

    ~Stopwatch()
    {
        if (ignore_result_) {
            return;
        }
        auto const end = std::chrono::steady_clock::now();
        auto const duration =
            std::chrono::duration_cast<Duration>(end - begin_);
        if (duration.count() >= min_) {
            LOG_DEBUG("{} {}", name_, duration);
        }
    }

    void ignore()
    {
        ignore_result_ = true;
    }
};

MONAD_NAMESPACE_END
