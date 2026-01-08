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

#include <boost/fiber/algo/algorithm.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/properties.hpp>
#include <boost/fiber/scheduler.hpp>

#include <chrono>
#include <cstdint>

struct io_uring;
struct io_uring_cqe;

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;
using boost::fibers::fiber_properties;

// Minimal properties for fibers - no priority needed
class FiberProperties final : public fiber_properties
{
public:
    explicit FiberProperties(context *const ctx) noexcept
        : fiber_properties{ctx}
    {
    }
};

// Completion token stored in io_uring sqe user_data.
// Allocated on fiber stack - remains valid while fiber is suspended.
// The magic number distinguishes fiber completions from other completions.
struct CompletionToken
{
    static constexpr uint64_t FIBER_COMPLETION_MAGIC = 0x4649424552434F4DULL; // "FIBERCOM"
    uint64_t magic{FIBER_COMPLETION_MAGIC};
    context *waiting_fiber{nullptr};
    int32_t result{0};
    bool completed{false};
};


// Custom Boost.Fiber scheduler for io_uring operations (reads and writes).
//
// When no fibers are ready, suspend_until() polls io_uring for completions
// and wakes waiting fibers. This integrates io_uring into the fiber scheduler
// so that fiber.join() works correctly without manual polling loops.
class UringFiberScheduler final
    : public boost::fibers::algo::algorithm_with_properties<FiberProperties>
{
    // The io_uring instances (borrowed, not owned)
    io_uring *rd_ring_;
    io_uring *wr_ring_;

    // Ready queue for fibers
    boost::fibers::scheduler::ready_queue_type ready_queue_{};

    // Count of ready fibers (excluding dispatcher)
    uint32_t ready_cnt_{0};

public:
    // Constructor takes both read and write rings.
    // They may be the same ring if using single-ring mode.
    explicit UringFiberScheduler(io_uring *rd_ring, io_uring *wr_ring);

    ~UringFiberScheduler() = default;

    UringFiberScheduler(UringFiberScheduler const &) = delete;
    UringFiberScheduler(UringFiberScheduler &&) = delete;
    UringFiberScheduler &operator=(UringFiberScheduler const &) = delete;
    UringFiberScheduler &operator=(UringFiberScheduler &&) = delete;

    // --- boost::fibers::algorithm interface ---

    // Called when a fiber becomes ready to run
    void awakened(context *ctx, FiberProperties &props) noexcept override;

    // Select the next fiber to run
    context *pick_next() noexcept override;

    // Check if there are ready fibers
    bool has_ready_fibers() const noexcept override;

    // Called by dispatcher when no fibers are ready - polls io_uring
    void suspend_until(
        std::chrono::steady_clock::time_point const &abs_time) noexcept override;

    // Called from other threads to wake the scheduler
    void notify() noexcept override;

private:
    // Poll a single ring for completions and wake waiting fibers.
    // Returns the number of completions processed.
    size_t poll_single_ring(io_uring *ring);

    // Wait on a ring with timeout, process any completion that arrives.
    // Returns true if a completion was processed.
    bool wait_on_ring(io_uring *ring);
};

MONAD_FIBER_NAMESPACE_END
