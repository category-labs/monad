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
#include <iterator>
#include <utility>

MONAD_NAMESPACE_BEGIN

/// A stack of versions of a value, one per frame that modified it.
///
/// Each entry is labelled with the version of the frame that created it.
/// State hands out versions in increasing order as frames are pushed and
/// never reuses one, so an entry belongs to the deepest open frame whose
/// version is at most its label. Accepting a frame therefore needs no work
/// on the stack: its entries simply belong to the parent from then on. Only
/// a reject pops entries, and compact() merges the entries of one frame
/// when the owner is known.
template <class T>
class VersionStack
{
    std::deque<std::pair<unsigned, T>> stack_{};

public:
    explicit VersionStack(T value, unsigned const version = 0)
    {
        stack_.emplace_back(version, std::move(value));
    }

    VersionStack(VersionStack &&) = default;
    VersionStack(VersionStack const &) = delete;
    VersionStack &operator=(VersionStack &&) = default;
    VersionStack &operator=(VersionStack const &) = delete;

    size_t size() const
    {
        return stack_.size();
    }

    /// An emptied stack stands for an account that a rejected frame
    /// re-seeded after an earlier reject; State erases entries only from the
    /// back of its map, so such an entry stays, empty.
    bool empty() const
    {
        return stack_.empty();
    }

    /// Re-seed an emptied stack with a base entry labelled `version`.
    void reset(T value, unsigned const version)
    {
        MONAD_ASSERT(stack_.empty());

        stack_.emplace_back(version, std::move(value));
    }

    /// Label of the top entry: the version of the frame that created it.
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

    /// Merge every entry belonging to `version` into one entry labelled
    /// `version`. The caller guarantees that no open frame has a version in
    /// (version, version()], i.e. that all entries labelled at or beyond
    /// `version` belong to it.
    void compact(unsigned const version)
    {
        MONAD_ASSERT(stack_.size());

        if (stack_.back().first <= version) {
            return;
        }
        auto const most_recent = std::prev(stack_.end());
        auto lowest = most_recent;
        while (lowest != stack_.begin() &&
               std::prev(lowest)->first >= version) {
            --lowest;
        }

        if (lowest != most_recent) {
            lowest->second = std::move(most_recent->second);
            stack_.erase(std::next(lowest), stack_.end());
        }
        lowest->first = version;
    }

    bool pop_reject(unsigned const version)
    {
        MONAD_ASSERT(version);

        while (!stack_.empty() && stack_.back().first >= version) {
            stack_.pop_back();
        }

        return stack_.empty();
    }
};

MONAD_NAMESPACE_END
