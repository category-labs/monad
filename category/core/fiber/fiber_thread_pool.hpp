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

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/mutex.hpp>

#include <atomic>
#include <functional>
#include <memory>
#include <thread>
#include <vector>

MONAD_FIBER_NAMESPACE_BEGIN

class FiberGroup;

/// FiberThreadPool manages a pool of OS threads that execute fibers.
/// Multiple FiberGroup instances can share the same FiberThreadPool,
/// allowing different fiber groups to execute on the same set of threads
/// via work-stealing through a shared PriorityQueue.
///
/// Architecture:
/// - One FiberThreadPool owns N OS threads and one PriorityQueue
/// - Multiple FiberGroup instances can be created from the pool
/// - Each FiberGroup has its own channel and fibers
/// - All fibers can migrate across threads via work-stealing
/// - This design reduces OS thread count while maintaining fiber parallelism
///
/// Destruction ordering: FiberGroups must be destroyed before the
/// FiberThreadPool they reference.
class FiberThreadPool final
{
    PriorityQueue queue_{};

    bool done_{false};

    boost::fibers::mutex mutex_{};
    boost::fibers::condition_variable cv_{};

    std::vector<std::thread> threads_{};

    // Track active fiber groups for safe destruction
    std::atomic<int> active_groups_{0};

    bool prevent_spin_;

    // Bootstrap channel for fiber creation requests
    // FiberGroups submit creation functions via this channel
    boost::fibers::buffered_channel<std::function<void()>> bootstrap_channel_{
        1024};

public:
    /// Create a thread pool with n_threads OS threads.
    /// \param n_threads Number of OS threads to create
    /// \param prevent_spin If true, threads will block instead of spin-waiting
    explicit FiberThreadPool(unsigned n_threads, bool prevent_spin = false);

    FiberThreadPool(FiberThreadPool const &) = delete;
    FiberThreadPool &operator=(FiberThreadPool const &) = delete;

    ~FiberThreadPool();

    /// Create a new FiberGroup that will execute fibers on this thread pool.
    /// The returned FiberGroup must be destroyed before this FiberThreadPool.
    /// \param n_fibers Number of fibers to create in the group
    /// \return Unique pointer to the new FiberGroup
    std::unique_ptr<FiberGroup> create_fiber_group(unsigned n_fibers);

    /// Get the number of OS threads in the pool
    unsigned num_threads() const
    {
        return static_cast<unsigned>(threads_.size());
    }

    friend class FiberGroup;

private:
    // Allow FiberGroup to access the shared queue
    PriorityQueue &queue()
    {
        return queue_;
    }

    bool prevent_spin() const
    {
        return prevent_spin_;
    }

    void submit_bootstrap_task(std::function<void()> task)
    {
        bootstrap_channel_.push(std::move(task));
    }

    void register_group()
    {
        active_groups_.fetch_add(1, std::memory_order_relaxed);
    }

    void unregister_group()
    {
        active_groups_.fetch_sub(1, std::memory_order_relaxed);
    }
};

MONAD_FIBER_NAMESPACE_END
