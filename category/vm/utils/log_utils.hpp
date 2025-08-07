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

#include <atomic>
#include <cmath>

template <class T>
concept Numeric = std::is_arithmetic_v<T>;

// not safe for concurrent updates
// can be safely read concurrent to updating
template <Numeric T>
struct EuclidMean
{
    std::atomic<T> running_avg_{0};
    std::atomic<T> count_{0};

    void update(T new_value) noexcept
    {
        auto count = count_.load(std::memory_order_acquire);
        auto running_avg = running_avg_.load(std::memory_order_acquire);
        auto new_avg = (running_avg * count + new_value) / (count + 1);
        running_avg_.store(new_avg, std::memory_order_release);
        count_.fetch_add(1, std::memory_order_release);
    }

    T get() const noexcept
    {
        return running_avg_.load(std::memory_order_acquire);
    }
};

// not safe for concurrent updates
// can be safely read concurrent to updating
template <Numeric T>
struct GeoMean
{
    std::atomic<T> running_avg_{0};
    std::atomic<T> count_{0};

    void update(T new_value) noexcept
    {
        auto count = count_.load(std::memory_order_acquire);
        auto running_avg = running_avg_.load(std::memory_order_acquire);
        auto new_avg =
            (running_avg * count + std::log2(new_value)) / (count + 1);
        running_avg_.store(new_avg, std::memory_order_release);
        count_.fetch_add(1, std::memory_order_release);
    }

    T get() const noexcept
    {
        return std::exp2(running_avg_.load(std::memory_order_acquire));
    }
};
