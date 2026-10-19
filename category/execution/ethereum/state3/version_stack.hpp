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

#include <cstddef>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
class VersionStack
{
    struct Node
    {
        std::pair<unsigned, T> entry;
        Node *previous;

        // Build the entry directly from the source so that no temporary T is
        // moved. Moving an immer container atomically increments the refcount
        // of an empty root that all threads share.
        Node(unsigned const version, T const &value, Node *const previous)
            : entry{version, value}
            , previous{previous}
        {
        }

        Node(unsigned const version, T &&value, Node *const previous)
            : entry{version, std::move(value)}
            , previous{previous}
        {
        }
    };

    // Every value lives in a stable node. Owner moves, including segmented-map
    // swap erase, transfer only the chain pointer and do not relocate T.
    Node *top_{};
    size_t size_{};

    unsigned back_version() const
    {
        return top_->entry.first;
    }

    T &back_value()
    {
        return top_->entry.second;
    }

    T const &back_value() const
    {
        return top_->entry.second;
    }

    void pop_back()
    {
        MONAD_ASSERT(size_);
        Node *const removed = top_;
        top_ = removed->previous;
        delete removed;
        --size_;
    }

    void clear() noexcept
    {
        // Avoid recursive destruction for an unusually deep call stack.
        while (top_) {
            Node *const removed = top_;
            top_ = removed->previous;
            delete removed;
        }
        size_ = 0;
    }

public:
    explicit VersionStack(T const &value, unsigned const version = 0)
        : top_{new Node{version, value, nullptr}}
        , size_{1}
    {
    }

    explicit VersionStack(T &&value, unsigned const version = 0)
        : top_{new Node{version, std::move(value), nullptr}}
        , size_{1}
    {
    }

    ~VersionStack()
    {
        clear();
    }

    VersionStack(VersionStack &&other) noexcept
        : top_{std::exchange(other.top_, nullptr)}
        , size_{std::exchange(other.size_, 0)}
    {
    }

    VersionStack(VersionStack const &) = delete;

    VersionStack &operator=(VersionStack &&other) noexcept
    {
        if (this != &other) {
            clear();
            top_ = std::exchange(other.top_, nullptr);
            size_ = std::exchange(other.size_, 0);
        }
        return *this;
    }

    VersionStack &operator=(VersionStack const &) = delete;

    size_t size() const
    {
        return size_;
    }

    unsigned version() const
    {
        MONAD_ASSERT(size_);
        return back_version();
    }

    T const &recent() const
    {
        MONAD_ASSERT(size_);
        return back_value();
    }

    T &recent()
    {
        MONAD_ASSERT(size_);
        return back_value();
    }

    T &current(unsigned const version)
    {
        MONAD_ASSERT(size_);

        if (version > back_version()) {
            top_ = new Node{version, back_value(), top_};
            ++size_;
        }

        return back_value();
    }

    void pop_accept(unsigned const version)
    {
        MONAD_ASSERT(version);
        MONAD_ASSERT(size_);

        if (version == back_version()) {
            if (top_->previous &&
                top_->previous->entry.first + 1 == top_->entry.first) {
                top_->previous->entry.second = std::move(top_->entry.second);
                pop_back();
            }
            else {
                top_->entry.first = version - 1;
            }
        }
    }

    bool pop_reject(unsigned const version)
    {
        MONAD_ASSERT(version);
        MONAD_ASSERT(size_);

        if (version == back_version()) {
            pop_back();
        }

        return size_ == 0;
    }
};

MONAD_NAMESPACE_END
