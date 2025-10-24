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
#include <category/core/fiber/priority_task.hpp>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/fiber.hpp>

#include <functional>
#include <future>
#include <vector>

MONAD_FIBER_NAMESPACE_BEGIN

class FiberThreadPool;

/// FiberGroup represents a group of fibers that execute on a shared
/// FiberThreadPool. Multiple FiberGroup instances can coexist on the same
/// thread pool, allowing different components to have their own task queues
/// and fiber limits while sharing the underlying OS threads.
///
/// Each FiberGroup has:
/// - Its own buffered_channel for task submission
/// - Its own set of fibers that process tasks from the channel
/// - Reference to a shared FiberThreadPool for thread resources
///
/// The fibers in this group can migrate to any thread in the pool via
/// work-stealing through the shared PriorityQueue.
///
/// FiberGroup must be destroyed before the FiberThreadPool it references.
class FiberGroup final
{
    FiberThreadPool &pool_;

    boost::fibers::buffered_channel<PriorityTask> channel_{1024};

    std::vector<boost::fibers::fiber> fibers_{};

    std::promise<void> start_{};

    friend class FiberThreadPool;

    FiberGroup(FiberThreadPool &pool, unsigned n_fibers);

public:
    FiberGroup(FiberGroup const &) = delete;
    FiberGroup &operator=(FiberGroup const &) = delete;

    ~FiberGroup();

    void submit(uint64_t const priority, std::function<void()> task)
    {
        channel_.push({priority, std::move(task)});
    }

    unsigned num_fibers() const
    {
        return static_cast<unsigned>(fibers_.size());
    }
};

MONAD_FIBER_NAMESPACE_END
