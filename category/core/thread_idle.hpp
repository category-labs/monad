// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/config.hpp>

#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <mutex>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

using IdleClock = uint64_t (*)() noexcept;

// CLOCK_MONOTONIC in nanoseconds; never 0 on a running system, which lets 0
// mean "not idle" below.
uint64_t monotonic_ns() noexcept;

// Cumulative time a busy-polling thread spent with nothing to do. Only the
// owning thread calls the mark_* functions and reset(); idle_ns() may be
// called from any thread.
class ThreadIdleCounter
{
    std::atomic<uint32_t> seq_{0}; // odd while the owner updates both fields
    std::atomic<uint64_t> idle_ns_total_{0}; // completed idle spans
    std::atomic<uint64_t> idle_since_ns_{0}; // 0 while busy
    IdleClock clock_{monotonic_ns};
    bool idle_{false}; // owner-thread only

public:
    ThreadIdleCounter() = default;
    explicit ThreadIdleCounter(IdleClock clock) noexcept;

    ThreadIdleCounter(ThreadIdleCounter const &) = delete;
    ThreadIdleCounter &operator=(ThreadIdleCounter const &) = delete;

    void mark_idle() noexcept;
    void mark_busy() noexcept;
    void mark_idle_at(uint64_t now_ns) noexcept;
    void mark_busy_at(uint64_t now_ns) noexcept;

    // Includes the span in progress at now_ns. If the owner stays mid-update
    // for the whole retry budget, returns completed spans only.
    uint64_t idle_ns(uint64_t now_ns) const noexcept;

    void reset(IdleClock clock) noexcept;
};

struct ThreadIdleSample
{
    std::array<char, 16> name; // NUL-terminated, at most 15 characters
    uint64_t idle_ns;
    uint64_t registered_at_ns; // on the registry's clock
};

// Raises each sample's idle_ns to at least that of the previous sample of the
// same registration (same name and registered_at_ns), if there is one.
void keep_idle_monotonic(
    std::span<ThreadIdleSample> current,
    std::span<ThreadIdleSample const> previous) noexcept;

// Process-wide table of busy-polling threads' idle counters.
class ThreadIdleRegistry
{
public:
    static constexpr size_t MAX_THREADS = 32;

    class Registration
    {
        ThreadIdleRegistry *registry_{nullptr};
        size_t slot_{0};

        Registration(
            ThreadIdleRegistry *const registry, size_t const slot) noexcept
            : registry_{registry}
            , slot_{slot}
        {
        }

        friend class ThreadIdleRegistry;

    public:
        Registration() = default;
        Registration(Registration &&other) noexcept;
        Registration &operator=(Registration &&other) noexcept;
        ~Registration();

        // nullptr when the registry was full: the thread runs uninstrumented.
        ThreadIdleCounter *counter() const noexcept;
    };

    explicit ThreadIdleRegistry(IdleClock clock = monotonic_ns) noexcept;

    ThreadIdleRegistry(ThreadIdleRegistry const &) = delete;
    ThreadIdleRegistry &operator=(ThreadIdleRegistry const &) = delete;

    static ThreadIdleRegistry &global() noexcept;

    // The calling thread becomes the owner of the returned counter.
    Registration claim(std::string_view name);

    size_t
    snapshot(std::span<ThreadIdleSample, MAX_THREADS> out) const noexcept;

private:
    // One cache line per owning thread.
    struct alignas(64) Slot
    {
        bool in_use{false};
        std::array<char, 16> name{}; // NUL-padded
        uint64_t registered_at_ns{0};
        ThreadIdleCounter counter;
    };

    static_assert(sizeof(Slot) % 64 == 0);

    IdleClock clock_;
    // Guards every Slot field except the counter state its owner writes.
    mutable std::mutex mutex_;
    std::array<Slot, MAX_THREADS> slots_{};

    void release(size_t slot) noexcept;
};

MONAD_NAMESPACE_END
