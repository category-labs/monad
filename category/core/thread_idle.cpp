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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/core/thread_idle.hpp>

#include <algorithm>
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <mutex>
#include <span>
#include <string_view>
#include <utility>

#include <time.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// A transition holds the seqlock for two stores, so exhausting this means the
// owner was descheduled mid-update.
constexpr unsigned SAMPLE_ATTEMPTS = 64;

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

uint64_t monotonic_ns() noexcept
{
    struct ::timespec ts;
    ::clock_gettime(CLOCK_MONOTONIC, &ts);
    return static_cast<uint64_t>(ts.tv_sec) * 1'000'000'000ULL +
           static_cast<uint64_t>(ts.tv_nsec);
}

void keep_idle_monotonic(
    std::span<ThreadIdleSample> const current,
    std::span<ThreadIdleSample const> const previous) noexcept
{
    for (ThreadIdleSample &sample : current) {
        auto const match =
            std::ranges::find_if(previous, [&](ThreadIdleSample const &prev) {
                return prev.registered_at_ns == sample.registered_at_ns &&
                       prev.name == sample.name;
            });
        if (match != previous.end()) {
            sample.idle_ns = std::max(sample.idle_ns, match->idle_ns);
        }
    }
}

ThreadIdleCounter::ThreadIdleCounter(IdleClock const clock) noexcept
    : clock_{clock}
{
}

void ThreadIdleCounter::mark_idle() noexcept
{
    if (!idle_) {
        mark_idle_at(clock_());
    }
}

void ThreadIdleCounter::mark_busy() noexcept
{
    if (idle_) {
        mark_busy_at(clock_());
    }
}

void ThreadIdleCounter::mark_idle_at(uint64_t const now_ns) noexcept
{
    MONAD_DEBUG_ASSERT(now_ns != 0);
    if (idle_) {
        return;
    }
    idle_ = true;
    // A lone store needs no seqlock: a sampler sees either side of it paired
    // with a consistent total.
    idle_since_ns_.store(now_ns, std::memory_order_relaxed);
}

void ThreadIdleCounter::mark_busy_at(uint64_t const now_ns) noexcept
{
    if (!idle_) {
        return;
    }
    idle_ = false;
    uint64_t const since = idle_since_ns_.load(std::memory_order_relaxed);
    uint64_t const span = now_ns > since ? now_ns - since : 0;
    uint32_t const seq = seq_.load(std::memory_order_relaxed);
    seq_.store(seq + 1, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_release);
    idle_ns_total_.store(
        idle_ns_total_.load(std::memory_order_relaxed) + span,
        std::memory_order_relaxed);
    idle_since_ns_.store(0, std::memory_order_relaxed);
    seq_.store(seq + 2, std::memory_order_release);
}

uint64_t ThreadIdleCounter::idle_ns(uint64_t const now_ns) const noexcept
{
    for (unsigned attempt = 0; attempt < SAMPLE_ATTEMPTS; ++attempt) {
        uint32_t const seq = seq_.load(std::memory_order_acquire);
        if (seq & 1U) {
            continue;
        }
        uint64_t const total = idle_ns_total_.load(std::memory_order_relaxed);
        uint64_t const since = idle_since_ns_.load(std::memory_order_relaxed);
        std::atomic_thread_fence(std::memory_order_acquire);
        if (seq_.load(std::memory_order_relaxed) != seq) {
            continue;
        }
        return total + (since != 0 && now_ns > since ? now_ns - since : 0);
    }
    return idle_ns_total_.load(std::memory_order_relaxed);
}

void ThreadIdleCounter::reset(IdleClock const clock) noexcept
{
    uint32_t const seq = seq_.load(std::memory_order_relaxed);
    seq_.store(seq + 1, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_release);
    idle_ns_total_.store(0, std::memory_order_relaxed);
    idle_since_ns_.store(0, std::memory_order_relaxed);
    seq_.store(seq + 2, std::memory_order_release);
    clock_ = clock;
    idle_ = false;
}

ThreadIdleRegistry::Registration::Registration(Registration &&other) noexcept
    : registry_{std::exchange(other.registry_, nullptr)}
    , slot_{other.slot_}
{
}

ThreadIdleRegistry::Registration &
ThreadIdleRegistry::Registration::operator=(Registration &&other) noexcept
{
    if (this != &other) {
        if (registry_ != nullptr) {
            registry_->release(slot_);
        }
        registry_ = std::exchange(other.registry_, nullptr);
        slot_ = other.slot_;
    }
    return *this;
}

ThreadIdleRegistry::Registration::~Registration()
{
    if (registry_ != nullptr) {
        registry_->release(slot_);
    }
}

ThreadIdleCounter *ThreadIdleRegistry::Registration::counter() const noexcept
{
    return registry_ != nullptr ? &registry_->slots_[slot_].counter : nullptr;
}

ThreadIdleRegistry::ThreadIdleRegistry(IdleClock const clock) noexcept
    : clock_{clock}
{
}

ThreadIdleRegistry &ThreadIdleRegistry::global() noexcept
{
    // Never destroyed: thread_local registrations can outlive static
    // destruction.
    alignas(ThreadIdleRegistry) static std::byte
        storage[sizeof(ThreadIdleRegistry)];
    static ThreadIdleRegistry *const registry =
        ::new (storage) ThreadIdleRegistry{};
    return *registry;
}

ThreadIdleRegistry::Registration
ThreadIdleRegistry::claim(std::string_view const name)
{
    {
        std::lock_guard const lock{mutex_};
        for (size_t i = 0; i < MAX_THREADS; ++i) {
            Slot &slot = slots_[i];
            if (slot.in_use) {
                continue;
            }
            slot.in_use = true;
            slot.name = {};
            std::memcpy(
                slot.name.data(),
                name.data(),
                std::min(name.size(), slot.name.size() - 1));
            slot.registered_at_ns = clock_();
            slot.counter.reset(clock_);
            return Registration{this, i};
        }
    }
    LOG_WARNING(
        "thread idle registry full ({} slots); {} is not instrumented",
        MAX_THREADS,
        name);
    return Registration{};
}

void ThreadIdleRegistry::release(size_t const slot) noexcept
{
    std::lock_guard const lock{mutex_};
    slots_[slot].in_use = false;
}

size_t ThreadIdleRegistry::snapshot(
    std::span<ThreadIdleSample, MAX_THREADS> const out) const noexcept
{
    uint64_t const now = clock_();
    std::lock_guard const lock{mutex_};
    size_t n = 0;
    for (Slot const &slot : slots_) {
        if (!slot.in_use) {
            continue;
        }
        ThreadIdleSample &sample = out[n++];
        sample.name = slot.name;
        sample.idle_ns = slot.counter.idle_ns(now);
        sample.registered_at_ns = slot.registered_at_ns;
    }
    return n;
}

MONAD_NAMESPACE_END
