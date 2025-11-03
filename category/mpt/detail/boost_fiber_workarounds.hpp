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

#include <category/core/tl_tid.h>
#include <category/core/unordered_map.hpp>

#include <boost/fiber/algo/round_robin.hpp>
#include <boost/fiber/fiber.hpp>

#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/fiber/future.hpp>
#ifdef __clang__
    #pragma clang diagnostic pop
#endif

#include <iostream>
#include <mutex>

#define MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING 1

MONAD_NAMESPACE_BEGIN

namespace detail
{
    template <class T>
    class threadsafe_boost_fibers_future
    {
        std::shared_ptr<
            std::pair<::boost::fibers::promise<T>, ::boost::fibers::future<T>>>
            state_;

    public:
        threadsafe_boost_fibers_future() = default;
        threadsafe_boost_fibers_future(threadsafe_boost_fibers_future const &) =
            delete;
        threadsafe_boost_fibers_future(threadsafe_boost_fibers_future &&) =
            default;

        explicit threadsafe_boost_fibers_future(
            std::shared_ptr<std::pair<
                ::boost::fibers::promise<T>, ::boost::fibers::future<T>>>
                state)
            : state_(std::move(state))
        {
        }

        threadsafe_boost_fibers_future &
        operator=(threadsafe_boost_fibers_future const &) = delete;
        threadsafe_boost_fibers_future &
        operator=(threadsafe_boost_fibers_future &&) = default;

        auto get()
        {
            return state_->second.get();
        }

        auto wait_for(auto const &dur)
        {
            return state_->second.wait_for(dur);
        }

        auto wait_until(auto const &dur)
        {
            return state_->second.wait_until(dur);
        }
    };
}

/*! \brief A threadsafe `boost::fibers::promise`.

Rather annoyingly when using Boost.Fibers promises across kernel threads,
if you destroy either side in the awoken kernel thread before the kernel
thread setting the value is done with the promise, you get a segfault.
This deeply unhelpful behaviour is worked around using a shared ptr.
*/
template <class T>
class threadsafe_boost_fibers_promise
{
    std::shared_ptr<
        std::pair<::boost::fibers::promise<T>, ::boost::fibers::future<T>>>
        state_;

public:
    threadsafe_boost_fibers_promise()
        : state_(
              std::make_shared<std::pair<
                  ::boost::fibers::promise<T>, ::boost::fibers::future<T>>>())
    {
    }

    threadsafe_boost_fibers_promise(threadsafe_boost_fibers_promise const &) =
        delete;
    threadsafe_boost_fibers_promise(threadsafe_boost_fibers_promise &&) =
        default;
    threadsafe_boost_fibers_promise &
    operator=(threadsafe_boost_fibers_promise const &) = delete;
    threadsafe_boost_fibers_promise &
    operator=(threadsafe_boost_fibers_promise &&) = default;
    ~threadsafe_boost_fibers_promise() = default;

    bool future_has_been_destroyed() const noexcept
    {
        return state_.use_count() == 1;
    }

    void reset()
    {
        state_ = std::make_shared<std::pair<
            ::boost::fibers::promise<T>,
            ::boost::fibers::future<T>>>();
    }

    auto get_future()
    {
        state_->second = state_->first.get_future();
        return detail::threadsafe_boost_fibers_future<T>(state_);
    }

    void set_exception(std::exception_ptr p)
    {
        state_->first.set_exception(std::move(p));
    }

    void set_value(T const &v)
    {
        state_->first.set_value(v);
    }

    void set_value(T &&v)
    {
        state_->first.set_value(std::move(v));
    }
};

template <>
class threadsafe_boost_fibers_promise<void>
{
    std::shared_ptr<std::pair<
        ::boost::fibers::promise<void>, ::boost::fibers::future<void>>>
        state_;

public:
    threadsafe_boost_fibers_promise()
        : state_(std::make_shared<std::pair<
                     ::boost::fibers::promise<void>,
                     ::boost::fibers::future<void>>>())
    {
    }

    threadsafe_boost_fibers_promise(threadsafe_boost_fibers_promise const &) =
        delete;
    threadsafe_boost_fibers_promise(threadsafe_boost_fibers_promise &&) =
        default;
    threadsafe_boost_fibers_promise &
    operator=(threadsafe_boost_fibers_promise const &) = delete;
    threadsafe_boost_fibers_promise &
    operator=(threadsafe_boost_fibers_promise &&) = default;
    ~threadsafe_boost_fibers_promise() = default;

    bool future_has_been_destroyed() const noexcept
    {
        return state_.use_count() == 1;
    }

    void reset()
    {
        state_ = std::make_shared<std::pair<
            ::boost::fibers::promise<void>,
            ::boost::fibers::future<void>>>();
    }

    auto get_future()
    {
        state_->second = state_->first.get_future();
        return detail::threadsafe_boost_fibers_future<void>(state_);
    }

    void set_exception(std::exception_ptr p)
    {
        state_->first.set_exception(std::move(p));
    }

    void set_value()
    {
        state_->first.set_value();
    }
};

MONAD_NAMESPACE_END
