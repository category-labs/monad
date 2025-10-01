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

#include <category/core/fiber/priority_pool.hpp>

#include <category/core/assert.h>
#include <category/core/fiber/config.hpp>
#include <category/core/fiber/priority_algorithm.hpp>
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_task.hpp>

#include <boost/fiber/channel_op_status.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/mutex.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/fiber/properties.hpp>
#include <boost/fiber/protected_fixedsize_stack.hpp>

#include <cstdio>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <utility>

#include <pthread.h>

MONAD_FIBER_NAMESPACE_BEGIN

PriorityPool::PriorityPool(
    std::string const &name_prefix, unsigned const n_threads,
    unsigned const n_fibers, bool const prevent_spin)
{
    MONAD_ASSERT(n_threads);
    MONAD_ASSERT(n_fibers);

    threads_.reserve(n_threads);
    for (unsigned i = n_threads - 1; i > 0; --i) {
        auto thread = std::thread([this, i, prevent_spin, name_prefix] {
            char name[16];
            std::snprintf(name, 16, "%sworker %u", name_prefix.c_str(), i);
            pthread_setname_np(pthread_self(), name);
            boost::fibers::use_scheduling_algorithm<PriorityAlgorithm>(
                queue_, prevent_spin);
            std::unique_lock<boost::fibers::mutex> lock{mutex_};
            cv_.wait(lock, [this] { return done_; });
        });
        threads_.push_back(std::move(thread));
    }

    fibers_.reserve(n_fibers);
    auto thread = std::thread([this, n_fibers, prevent_spin, name_prefix] {
        char name[16];
        std::snprintf(name, 16, "%sworker %u", name_prefix.c_str(), 0);
        pthread_setname_np(pthread_self(), name);
        boost::fibers::use_scheduling_algorithm<PriorityAlgorithm>(
            queue_, prevent_spin);
        for (unsigned i = 0; i < n_fibers; ++i) {
            auto *const properties = new PriorityProperties{nullptr};
            boost::fibers::fiber fiber{
                static_cast<boost::fibers::fiber_properties *>(properties),
                std::allocator_arg,
                boost::fibers::protected_fixedsize_stack{
                    static_cast<size_t>(8 * 1024 * 1024)},
                [this, properties] {
                    PriorityTask task;
                    while (channel_.pop(task) ==
                           boost::fibers::channel_op_status::success) {
                        properties->set_priority(task.priority);
                        boost::this_fiber::yield();
                        task.task();
                        properties->set_priority(0);
                    }
                }};
            fibers_.push_back(std::move(fiber));
        }
        start_.set_value();
        std::unique_lock<boost::fibers::mutex> lock{mutex_};
        cv_.wait(lock, [this] { return done_; });
    });
    threads_.push_back(std::move(thread));
}

PriorityPool::~PriorityPool()
{
    channel_.close();

    start_.get_future().wait();

    while (fibers_.size()) {
        auto &fiber = fibers_.back();
        fiber.join();
        fibers_.pop_back();
    }

    {
        std::unique_lock<boost::fibers::mutex> const lock{mutex_};
        done_ = true;
    }

    cv_.notify_all();

    while (threads_.size()) {
        auto &thread = threads_.back();
        thread.join();
        threads_.pop_back();
    }
}

MONAD_FIBER_NAMESPACE_END
