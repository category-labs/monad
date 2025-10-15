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
#include <category/core/fiber/priority_properties.hpp>
#include <category/core/fiber/priority_queue.hpp>

#include <boost/fiber/algo/algorithm.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/scheduler.hpp>

#include <chrono>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;

class PriorityAlgorithm final
    : public boost::fibers::algo::algorithm_with_properties<PriorityProperties>
{
    bool recent_{true};
    // if set true, threads do not spin when no fiber available
    bool prevent_spin_{false};

    PriorityQueue &rqueue_;

    using lqueue_type = boost::fibers::scheduler::ready_queue_type;

    lqueue_type lqueue_{};

public:
    explicit PriorityAlgorithm(PriorityQueue &, bool prevent_spin = false);

    PriorityAlgorithm(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm(PriorityAlgorithm &&) = delete;

    PriorityAlgorithm &operator=(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm &operator=(PriorityAlgorithm &&) = delete;

    using boost::fibers::algo::algorithm_with_properties<PriorityProperties>::awakened;

    void awakened(context *, PriorityProperties &) noexcept override;

    context *pick_next() noexcept override;

    bool has_ready_fibers() const noexcept override;

    void suspend_until(
        std::chrono::steady_clock::time_point const &) noexcept override
    {
    }

    void notify() noexcept override {}
};

MONAD_FIBER_NAMESPACE_END
