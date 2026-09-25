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

#include <category/core/thread_idle.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <thread>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    std::atomic<uint64_t> fake_now{0};
    std::atomic<unsigned> fake_reads{0};

    uint64_t fake_clock() noexcept
    {
        fake_reads.fetch_add(1, std::memory_order_relaxed);
        return fake_now.load(std::memory_order_relaxed);
    }

    struct ThreadIdleCounterTest : public ::testing::Test
    {
        void SetUp() override
        {
            fake_now = 1000;
            fake_reads = 0;
        }
    };
}

TEST_F(ThreadIdleCounterTest, starts_busy_with_no_idle_time)
{
    ThreadIdleCounter const c{fake_clock};
    EXPECT_EQ(c.idle_ns(5000), 0u);
}

TEST_F(ThreadIdleCounterTest, accumulates_completed_idle_spans)
{
    ThreadIdleCounter c{fake_clock};
    c.mark_idle();
    fake_now = 1500;
    c.mark_busy();
    fake_now = 2000;
    c.mark_idle();
    fake_now = 2300;
    c.mark_busy();
    EXPECT_EQ(c.idle_ns(9999), 800u);
}

TEST_F(ThreadIdleCounterTest, includes_the_span_in_progress)
{
    ThreadIdleCounter c{fake_clock};
    c.mark_idle();
    EXPECT_EQ(c.idle_ns(1700), 700u);
}

TEST_F(
    ThreadIdleCounterTest, a_span_starting_after_the_sample_time_adds_nothing)
{
    ThreadIdleCounter c{fake_clock};
    fake_now = 2000;
    c.mark_idle();
    EXPECT_EQ(c.idle_ns(1500), 0u);
}

TEST_F(ThreadIdleCounterTest, reads_the_clock_only_on_transitions)
{
    ThreadIdleCounter c{fake_clock};
    for (int i = 0; i < 3; ++i) {
        c.mark_busy();
    }
    EXPECT_EQ(fake_reads.load(), 0u);
    for (int i = 0; i < 5; ++i) {
        c.mark_idle();
    }
    EXPECT_EQ(fake_reads.load(), 1u);
    for (int i = 0; i < 5; ++i) {
        c.mark_busy();
    }
    EXPECT_EQ(fake_reads.load(), 2u);
}

TEST_F(ThreadIdleCounterTest, explicit_timestamps_bypass_the_clock)
{
    ThreadIdleCounter c{fake_clock};
    c.mark_idle_at(100);
    c.mark_idle_at(150); // already idle: the span still starts at 100
    c.mark_busy_at(400);
    c.mark_busy_at(900);
    EXPECT_EQ(c.idle_ns(10'000), 300u);
    EXPECT_EQ(fake_reads.load(), 0u);
}

TEST_F(ThreadIdleCounterTest, reset_restarts_at_zero)
{
    ThreadIdleCounter c{fake_clock};
    c.mark_idle();
    fake_now = 5000;
    c.mark_busy();
    c.mark_idle();
    c.reset(fake_clock);
    EXPECT_EQ(c.idle_ns(9000), 0u);
    c.mark_idle(); // reset left it busy, so this is a transition
    EXPECT_EQ(c.idle_ns(5100), 100u);
}

TEST(ThreadIdleCounter, concurrent_samples_never_exceed_elapsed_time)
{
    ThreadIdleCounter c;
    uint64_t const start = monotonic_ns();
    std::atomic<bool> done{false};
    std::thread owner{[&] {
        for (int i = 0; i < 200'000; ++i) {
            c.mark_idle();
            c.mark_busy();
        }
        done.store(true, std::memory_order_release);
    }};
    bool exceeded = false;
    while (!done.load(std::memory_order_acquire) && !exceeded) {
        uint64_t const now = monotonic_ns();
        exceeded = c.idle_ns(now) > now - start;
    }
    owner.join();
    EXPECT_FALSE(exceeded) << "a sample double-counted an idle span";
}

TEST(ThreadIdleCounter, torn_samples_would_exceed_synthetic_elapsed_time)
{
    ThreadIdleCounter c{fake_clock};
    std::atomic<uint64_t> synthetic_now{1};
    std::atomic<bool> done{false};
    std::thread owner{[&] {
        c.mark_idle_at(synthetic_now.load(std::memory_order_relaxed));
        for (int i = 0; i < 200'000; ++i) {
            uint64_t const t = synthetic_now.fetch_add(1000) + 1000;
            c.mark_busy_at(t); // zero-length: true idle equals elapsed time
            c.mark_idle_at(t);
        }
        done.store(true, std::memory_order_release);
    }};
    bool exceeded = false;
    while (!done.load(std::memory_order_acquire) && !exceeded) {
        uint64_t const now = synthetic_now.load(std::memory_order_relaxed);
        uint64_t const idle = c.idle_ns(now);
        uint64_t const after = synthetic_now.load(std::memory_order_relaxed);
        exceeded = idle > after - 1;
    }
    owner.join();
    EXPECT_FALSE(exceeded) << "a torn sample overshot the synthetic elapsed "
                              "time";
}

namespace
{
    using Samples =
        std::array<ThreadIdleSample, ThreadIdleRegistry::MAX_THREADS>;

    std::string name_of(ThreadIdleSample const &s)
    {
        return std::string{s.name.data()};
    }

    struct ThreadIdleRegistryTest : public ThreadIdleCounterTest
    {
    };
}

TEST_F(ThreadIdleRegistryTest, a_claim_is_sampled_with_its_name_and_start)
{
    ThreadIdleRegistry registry{fake_clock};
    auto const reg = registry.claim("ftpool 0");
    ASSERT_NE(reg.counter(), nullptr);

    Samples out;
    ASSERT_EQ(registry.snapshot(out), 1u);
    EXPECT_EQ(name_of(out[0]), "ftpool 0");
    EXPECT_EQ(out[0].registered_at_ns, 1000u);
    EXPECT_EQ(out[0].idle_ns, 0u);
}

TEST_F(ThreadIdleRegistryTest, snapshot_includes_the_idle_span_in_progress)
{
    ThreadIdleRegistry registry{fake_clock};
    auto const reg = registry.claim("triedb rw");
    reg.counter()->mark_idle();
    fake_now = 1400;

    Samples out;
    ASSERT_EQ(registry.snapshot(out), 1u);
    EXPECT_EQ(out[0].idle_ns, 400u);
}

TEST_F(ThreadIdleRegistryTest, a_released_slot_leaves_the_snapshot)
{
    ThreadIdleRegistry registry{fake_clock};
    {
        auto const reg = registry.claim("gone");
    }
    Samples out;
    EXPECT_EQ(registry.snapshot(out), 0u);
}

TEST_F(ThreadIdleRegistryTest, a_reused_slot_starts_from_zero)
{
    ThreadIdleRegistry registry{fake_clock};
    {
        auto const reg = registry.claim("first");
        reg.counter()->mark_idle();
        fake_now = 9000;
    }
    auto const reg = registry.claim("second");
    Samples out;
    ASSERT_EQ(registry.snapshot(out), 1u);
    EXPECT_EQ(name_of(out[0]), "second");
    EXPECT_EQ(out[0].idle_ns, 0u);
    EXPECT_EQ(out[0].registered_at_ns, 9000u);
}

TEST_F(ThreadIdleRegistryTest, long_names_are_truncated_to_fifteen_characters)
{
    ThreadIdleRegistry registry{fake_clock};
    auto const reg = registry.claim("0123456789abcdefXYZ");
    Samples out;
    ASSERT_EQ(registry.snapshot(out), 1u);
    EXPECT_EQ(name_of(out[0]), "0123456789abcde");
    EXPECT_EQ(out[0].name[15], '\0');
}

TEST_F(ThreadIdleRegistryTest, a_full_registry_hands_out_uninstrumented_claims)
{
    ThreadIdleRegistry registry{fake_clock};
    std::vector<ThreadIdleRegistry::Registration> regs;
    for (size_t i = 0; i < ThreadIdleRegistry::MAX_THREADS; ++i) {
        regs.push_back(registry.claim("t"));
        ASSERT_NE(regs.back().counter(), nullptr);
    }
    auto const overflow = registry.claim("overflow");
    EXPECT_EQ(overflow.counter(), nullptr);

    Samples out;
    EXPECT_EQ(registry.snapshot(out), ThreadIdleRegistry::MAX_THREADS);
}

TEST_F(ThreadIdleRegistryTest, a_moved_from_registration_does_not_release)
{
    ThreadIdleRegistry registry{fake_clock};
    std::optional<ThreadIdleRegistry::Registration> kept;
    {
        auto reg = registry.claim("moved");
        kept.emplace(std::move(reg));
    }
    Samples out;
    EXPECT_EQ(registry.snapshot(out), 1u);
    kept.reset();
    EXPECT_EQ(registry.snapshot(out), 0u);
}

namespace
{
    ThreadIdleSample make_sample(
        std::string_view const name, uint64_t const idle_ns,
        uint64_t const registered_at_ns)
    {
        ThreadIdleSample s{};
        std::memcpy(
            s.name.data(),
            name.data(),
            std::min(name.size(), s.name.size() - 1));
        s.idle_ns = idle_ns;
        s.registered_at_ns = registered_at_ns;
        return s;
    }
}

TEST(KeepIdleMonotonic, a_decrease_is_held_at_the_previous_value)
{
    std::array const previous{make_sample("triedb rw", 500, 10)};
    std::array current{make_sample("triedb rw", 480, 10)};
    keep_idle_monotonic(current, previous);
    EXPECT_EQ(current[0].idle_ns, 500u);
}

TEST(KeepIdleMonotonic, an_increase_passes_through)
{
    std::array const previous{make_sample("triedb rw", 500, 10)};
    std::array current{make_sample("triedb rw", 700, 10)};
    keep_idle_monotonic(current, previous);
    EXPECT_EQ(current[0].idle_ns, 700u);
}

TEST(KeepIdleMonotonic, a_new_registration_under_the_same_name_is_not_clamped)
{
    std::array const previous{make_sample("triedb rw", 500, 10)};
    std::array current{make_sample("triedb rw", 3, 20)};
    keep_idle_monotonic(current, previous);
    EXPECT_EQ(current[0].idle_ns, 3u);
}

TEST(KeepIdleMonotonic, a_sample_absent_from_previous_is_untouched)
{
    std::array const previous{make_sample("ftpool 0", 500, 10)};
    std::array current{
        make_sample("ftpool 1", 7, 10), make_sample("ftpool 0", 400, 10)};
    keep_idle_monotonic(current, previous);
    EXPECT_EQ(current[0].idle_ns, 7u);
    EXPECT_EQ(current[1].idle_ns, 500u);
}
