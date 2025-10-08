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

#include <category/core/assert.h>
#include <category/core/config.hpp>

#include <deque>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
class VersionStack
{
    std::deque<std::pair<unsigned, T>> stack_{};

public:
    VersionStack(T value, unsigned version = 0)
    {
        stack_.emplace_back(version, std::move(value));
    }

    VersionStack(VersionStack &&) = default;
    VersionStack(VersionStack const &) = delete;
    VersionStack &operator=(VersionStack &&) = default;
    VersionStack &operator=(VersionStack const &) = delete;

    void reset(T value, unsigned version = 0)
    {
        stack_.clear();
        stack_.emplace_back(version, std::move(value));
    }

    size_t size() const
    {
        return stack_.size();
    }

    unsigned version() const
    {
        MONAD_ASSERT(stack_.size());

        return stack_.back().first;
    }

    T const &recent() const
    {
        MONAD_ASSERT(stack_.size());

        return stack_.back().second;
    }

    T &recent()
    {
        MONAD_ASSERT(stack_.size());

        return stack_.back().second;
    }

    T &current(unsigned const version)
    {
        MONAD_ASSERT(stack_.size());

        if (version > stack_.back().first) {
            T value = stack_.back().second;
            stack_.emplace_back(version, std::move(value));
        }

        return stack_.back().second;
    }

    void pop_accept(unsigned const version)
    {
        MONAD_ASSERT(version);

        auto const size = stack_.size();
        MONAD_ASSERT(size);

        if (version == stack_.back().first) {
            if (size > 1 &&
                stack_[size - 2].first + 1 == stack_[size - 1].first) {
                stack_[size - 2].second = std::move(stack_[size - 1].second);
                stack_.pop_back();
            }
            else {
                stack_.back().first = version - 1;
            }
        }
    }

    bool pop_reject(unsigned const version)
    {
        MONAD_ASSERT(version);

        auto const size = stack_.size();
        MONAD_ASSERT(size);

        if (version == stack_.back().first) {
            stack_.pop_back();
        }

        return stack_.empty();
    }
};

MONAD_NAMESPACE_END
