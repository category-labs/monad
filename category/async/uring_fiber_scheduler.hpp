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

namespace monad::async
{
class AsyncIO;
}

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;
using boost::fibers::fiber_properties;

class FiberProperties final : public fiber_properties
{
public:
    explicit FiberProperties(context *const ctx) noexcept
        : fiber_properties{ctx}
    {
    }
};

// Stored in io_uring sqe user_data. Allocated on fiber stack.
struct CompletionToken
{
    // Distinguishes fiber completions from erased_connected_operation*
    static constexpr uint64_t FIBER_COMPLETION_MAGIC = 0x4649424552434F4DULL;

    uint64_t magic{FIBER_COMPLETION_MAGIC};
    context *waiting_fiber{nullptr};
    int32_t result{0};
    bool completed{false};
};

class UringFiberScheduler final
    : public boost::fibers::algo::algorithm_with_properties<FiberProperties>
{
    monad::async::AsyncIO *io_;
    boost::fibers::scheduler::ready_queue_type ready_queue_{};
    uint32_t ready_cnt_{0};

public:
    explicit UringFiberScheduler(monad::async::AsyncIO *io);

    ~UringFiberScheduler() = default;

    UringFiberScheduler(UringFiberScheduler const &) = delete;
    UringFiberScheduler(UringFiberScheduler &&) = delete;
    UringFiberScheduler &operator=(UringFiberScheduler const &) = delete;
    UringFiberScheduler &operator=(UringFiberScheduler &&) = delete;

    void awakened(context *ctx, FiberProperties &props) noexcept override;
    context *pick_next() noexcept override;
    bool has_ready_fibers() const noexcept override;
    void
    suspend_until(std::chrono::steady_clock::time_point const &) noexcept override;
    void notify() noexcept override;
};

MONAD_FIBER_NAMESPACE_END
