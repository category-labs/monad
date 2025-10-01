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

#include <category/core/fiber/config.hpp>
#include <category/core/fiber/priority_queue.hpp>
#include <category/core/fiber/priority_task.hpp>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/mutex.hpp>

#include <future>
#include <string>
#include <thread>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool final
{
    PriorityQueue queue_{};

    bool done_{false};

    boost::fibers::mutex mutex_{};
    boost::fibers::condition_variable cv_{};

    std::vector<std::thread> threads_{};

    boost::fibers::buffered_channel<PriorityTask> channel_{1024};

    std::vector<boost::fibers::fiber> fibers_{};

    std::promise<void> start_{};

public:
    PriorityPool(
        std::string const &name_prefix, unsigned n_threads, unsigned n_fibers,
        bool prevent_spin = false);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    void submit(uint64_t const priority, std::function<void()> task)
    {
        channel_.push({priority, std::move(task)});
    }
};

MONAD_FIBER_NAMESPACE_END
