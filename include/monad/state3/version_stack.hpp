#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>

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
