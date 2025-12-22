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

#include <category/core/fiber/fiber_group.hpp>

#include <category/core/assert.h>
#include <category/core/fiber/config.hpp>
#include <category/core/fiber/fiber_thread_pool.hpp>
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_task.hpp>
#include <category/core/runtime/non_temporal_memory.hpp>

#include <boost/fiber/channel_op_status.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/fiber/protected_fixedsize_stack.hpp>

#include <cstddef>
#include <future>
#include <memory>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

FiberGroup::FiberGroup(FiberThreadPool &pool, unsigned const n_fibers)
    : pool_{pool}
{
    MONAD_ASSERT(n_fibers);

    pool_.register_group();
    fibers_.reserve(n_fibers);
    vm_memory_.reserve(n_fibers);

    for (unsigned i = 0; i < n_fibers; ++i) {
        vm_memory_.emplace_back(8 * 1024 * 1024);
    }

    // Create fibers via bootstrap channel so they're created on a thread with
    // the proper scheduler configured.
    pool_.submit_bootstrap_task([this, n_fibers] {
        for (unsigned i = 0; i < n_fibers; ++i) {
            auto *const properties = new PriorityProperties{nullptr};
            boost::fibers::fiber fiber{
                static_cast<boost::fibers::fiber_properties *>(properties),
                std::allocator_arg,
                boost::fibers::protected_fixedsize_stack{
                    static_cast<size_t>(8 * 1024 * 1024)},
                [this, i, properties] {
                    PriorityTask task;
                    while (channel_.pop(task) ==
                           boost::fibers::channel_op_status::success) {
                        properties->set_priority(task.priority);
                        boost::this_fiber::yield();
                        task.task(vm_memory_[i]);
                        properties->set_priority(0);
                    }
                }};
            fibers_.push_back(std::move(fiber));
        }
        start_.set_value();
    });

    start_.get_future().wait();
}

FiberGroup::~FiberGroup()
{
    channel_.close();

    while (fibers_.size()) {
        auto &fiber = fibers_.back();
        fiber.join();
        fibers_.pop_back();
    }

    pool_.unregister_group();
}

MONAD_FIBER_NAMESPACE_END
