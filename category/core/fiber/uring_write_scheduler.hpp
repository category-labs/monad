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

// Minimal properties for write fibers - no priority needed since writes are
// serialized
class WriteProperties final : public fiber_properties
{
public:
    explicit WriteProperties(context *const ctx) noexcept
        : fiber_properties{ctx}
    {
    }
};

// Completion token stored in io_uring sqe user_data.
// Allocated on fiber stack - remains valid while fiber is suspended.
struct WriteCompletionToken
{
    context *waiting_fiber{nullptr};
    int32_t result{0};
    bool completed{false};
};

// Custom Boost.Fiber scheduler for io_uring write operations.
//
// Designed following the helio FiberSchedAlgo pattern:
// - Main context (io loop fiber) polls io_uring for completions
// - Worker fibers yield when waiting for IO
// - Completions wake suspended fibers via awakened()
//
// This scheduler is separate from PriorityAlgorithm used for reads,
// dedicated to database write operations on a single thread.
class UringWriteFiberScheduler final
    : public boost::fibers::algo::algorithm_with_properties<WriteProperties>
{
public:
    // State flags tracking io loop fiber state (similar to helio pattern)
    struct Flags
    {
        uint8_t ioloop_suspended : 1;
        uint8_t ioloop_yielded : 1;
        uint8_t ioloop_woke : 1;
        uint8_t suspenduntil_called : 1;

        constexpr Flags() noexcept
            : ioloop_suspended{0}
            , ioloop_yielded{0}
            , ioloop_woke{0}
            , suspenduntil_called{0}
        {
        }
    };

private:
    // The io_uring instance for writes (borrowed, not owned)
    io_uring *wr_ring_;

    // The main context - the io loop fiber that polls io_uring
    context *main_cntx_;

    // Ready queue for fibers
    boost::fibers::scheduler::ready_queue_type ready_queue_{};

    // Count of ready fibers (excluding dispatcher)
    uint32_t ready_cnt_{0};

    // State flags
    Flags flags_{};

    // Shutdown flag
    bool done_{false};

public:
    // Constructor must be called from the thread that will run the scheduler,
    // as it captures the active context as main_cntx_
    explicit UringWriteFiberScheduler(io_uring *wr_ring);

    // Thread-local reference to the current thread's scheduler (if any).
    // Set during construction, used for cleanup before thread exit.
    static inline thread_local UringWriteFiberScheduler *current_scheduler =
        nullptr;

    ~UringWriteFiberScheduler()
    {
        // Mark done before base class destructor runs, which may call pick_next
        done_ = true;
        // Clear thread-local reference to prevent access after destruction
        current_scheduler = nullptr;
        // Null out ring pointer to catch any errant access
        wr_ring_ = nullptr;
    }

    UringWriteFiberScheduler(UringWriteFiberScheduler const &) = delete;
    UringWriteFiberScheduler(UringWriteFiberScheduler &&) = delete;
    UringWriteFiberScheduler &operator=(UringWriteFiberScheduler const &) =
        delete;
    UringWriteFiberScheduler &operator=(UringWriteFiberScheduler &&) = delete;

    // --- boost::fibers::algorithm interface ---

    // Called when a fiber becomes ready to run
    void awakened(context *ctx, WriteProperties &props) noexcept override;

    // Select the next fiber to run
    context *pick_next() noexcept override;

    // Check if there are ready fibers
    bool has_ready_fibers() const noexcept override;

    // Called by dispatcher when no fibers are ready
    void suspend_until(
        std::chrono::steady_clock::time_point const &abs_time) noexcept override;

    // Called from other threads to wake the scheduler
    void notify() noexcept override;

    // --- io_uring integration ---

    // Poll io_uring for completions and wake waiting fibers.
    // If blocking is true, waits for at least one completion.
    // Returns the number of completions processed.
    size_t poll_completions(bool blocking);

    // Mark this scheduler as done (for shutdown)
    void set_done() noexcept
    {
        done_ = true;
    }

    [[nodiscard]] bool is_done() const noexcept
    {
        return done_;
    }

    // Access the io_uring ring (for fiber_write functions)
    [[nodiscard]] io_uring *ring() const noexcept
    {
        return wr_ring_;
    }

    // Get count of ready fibers
    [[nodiscard]] uint32_t ready_count() const noexcept
    {
        return ready_cnt_;
    }

private:
    // Process a single completion queue entry and wake the waiting fiber
    void process_cqe(::io_uring_cqe *cqe);

    // Check if main context should yield to other fibers
    [[nodiscard]] bool main_has_switched() const noexcept
    {
        return flags_.ioloop_suspended && flags_.ioloop_yielded;
    }
};

MONAD_FIBER_NAMESPACE_END
