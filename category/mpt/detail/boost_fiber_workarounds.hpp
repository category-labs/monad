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

namespace detail
{
    struct debugging_fiber_scheduler_algorithm_wrapper_shared_state_t
    {
        std::mutex lock;
        unordered_dense_map<pid_t, unordered_flat_set<boost::fibers::context *>>
            tid_to_fibers;
        unordered_flat_map<boost::fibers::context *, pid_t> fiber_to_tid;
    };

    extern inline __attribute__((visibility("default")))
    debugging_fiber_scheduler_algorithm_wrapper_shared_state_t &
    debugging_fiber_scheduler_algorithm_wrapper_shared_state()
    {
        static debugging_fiber_scheduler_algorithm_wrapper_shared_state_t v;
        return v;
    }
}

/*! \brief Non-hanging Boost.Fiber scheduler

When multiple kernel threads use Boost.Fiber objects, you can get random
hangs. This custom Fiber scheduler works around those issues.
*/
template <class BaseFiberScheduler>
class debugging_fiber_scheduler_algorithm_wrapper : public BaseFiberScheduler
{
    virtual void awakened(boost::fibers::context *ctx) noexcept override
    {
        {
            auto const mytid = get_tl_tid();
            auto &state = detail::
                debugging_fiber_scheduler_algorithm_wrapper_shared_state();
            std::lock_guard g(state.lock);
            auto it = state.fiber_to_tid.find(ctx);
            if (it == state.fiber_to_tid.end()) {
                state.fiber_to_tid[ctx] = mytid;
                state.tid_to_fibers[mytid].insert(ctx);
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
                std::cerr << "awakened(): Boost fiber " << ctx
                          << " is awakened for first time on thread " << mytid
                          << std::endl;
#endif
            }
            else if (it->second != mytid) {
                // fiber has changed kernel thread
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
                std::cerr << "awakened(): Boost fiber " << ctx
                          << " is moved from thread " << it->second
                          << " to thread " << mytid << std::endl;
#endif
                state.tid_to_fibers[it->second].erase(ctx);
                state.fiber_to_tid[ctx] = mytid;
                state.tid_to_fibers[mytid].insert(ctx);
            }
            else {
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
                std::cerr << "awakened(): Boost fiber " << ctx
                          << " is resumed on thread " << mytid << std::endl;
#endif
            }
        }
        BaseFiberScheduler::awakened(ctx);
    }

    virtual boost::fibers::context *pick_next() noexcept override
    {
        auto *ctx = BaseFiberScheduler::pick_next();
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
        auto const mytid = get_tl_tid();
        auto &state =
            detail::debugging_fiber_scheduler_algorithm_wrapper_shared_state();
        std::lock_guard g(state.lock);
        std::cerr << "pick_next(): Boost fiber " << ctx
                  << " is picked for thread " << mytid << std::endl;
#endif
        return ctx;
    }

    virtual bool has_ready_fibers() const noexcept override
    {
        return BaseFiberScheduler::has_ready_fibers();
    }

    virtual void suspend_until(
        std::chrono::steady_clock::time_point const &tm) noexcept override
    {
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
        auto const mytid = get_tl_tid();
        auto &state =
            detail::debugging_fiber_scheduler_algorithm_wrapper_shared_state();
        std::lock_guard g(state.lock);
        std::cerr << "suspend_until(): for thread " << mytid << std::endl;
#endif
        BaseFiberScheduler::suspend_until(tm);
    }

    virtual void notify() noexcept override
    {
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
        auto const mytid = get_tl_tid();
        auto &state =
            detail::debugging_fiber_scheduler_algorithm_wrapper_shared_state();
        std::lock_guard g(state.lock);
        std::cerr << "notify(): for thread " << mytid << std::endl;
#endif
        BaseFiberScheduler::notify();
    }

public:
    debugging_fiber_scheduler_algorithm_wrapper()
    {
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
        auto const mytid = get_tl_tid();
        auto &state =
            detail::debugging_fiber_scheduler_algorithm_wrapper_shared_state();
        std::lock_guard g(state.lock);
        std::cerr << "Fiber scheduler constructs for thread " << mytid
                  << std::endl;
#endif
    }

    ~debugging_fiber_scheduler_algorithm_wrapper()
    {
        auto const mytid = get_tl_tid();
        auto &state =
            detail::debugging_fiber_scheduler_algorithm_wrapper_shared_state();
        std::lock_guard g(state.lock);
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
        std::cerr << "Fiber scheduler destructs for thread " << mytid
                  << std::endl;
#endif
        auto it = state.tid_to_fibers.find(mytid);
        if (it != state.tid_to_fibers.end()) {
            for (auto *ctx : it->second) {
#if MONAD_BOOST_FIBER_WORKAROUNDS_DEBUG_PRINTING
                std::cerr << "   Fiber " << ctx << " is detached" << std::endl;
#endif
                state.fiber_to_tid.erase(ctx);
            }
            state.tid_to_fibers.erase(it);
        }
    }
};

template <class BaseFiberScheduler = ::boost::fibers::algo::round_robin>
inline void use_debugging_fiber_scheduler_wrapper()
{
    ::boost::fibers::use_scheduling_algorithm<
        debugging_fiber_scheduler_algorithm_wrapper<BaseFiberScheduler>>();
}

MONAD_NAMESPACE_END
