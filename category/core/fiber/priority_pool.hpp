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
#include <category/core/fiber/fiber_group.hpp>
#include <category/core/fiber/fiber_thread_pool.hpp>

#include <functional>
#include <memory>

MONAD_FIBER_NAMESPACE_BEGIN

/// PriorityPool is a convenience wrapper that combines a dedicated
/// FiberThreadPool with a single FiberGroup.
///
/// This provides a simple interface for creating an isolated pool of threads
/// and fibers for executing prioritized tasks. For scenarios where multiple
/// fiber groups should share threads, use FiberThreadPool::create_fiber_group()
/// directly.
class PriorityPool final
{
    std::unique_ptr<FiberThreadPool> thread_pool_;
    std::unique_ptr<FiberGroup> fiber_group_;

public:
    PriorityPool(
        unsigned n_threads, unsigned n_fibers, bool prevent_spin = false);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool() = default;

    unsigned num_fibers() const
    {
        return fiber_group_->num_fibers();
    }

    unsigned num_threads() const
    {
        return thread_pool_->num_threads();
    }

    void submit(uint64_t const priority, std::function<void()> task)
    {
        fiber_group_->submit(priority, std::move(task));
    }

    FiberGroup &fiber_group()
    {
        return *fiber_group_;
    }
};

MONAD_FIBER_NAMESPACE_END
