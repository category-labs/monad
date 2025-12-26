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

#include <category/vm/memory_pool.hpp>

#include <gtest/gtest.h>

#include <array>
#include <atomic>
#include <thread>

using namespace monad::vm;

static constexpr size_t N = 1'000;

TEST(MonadVmMemoryPool, stress_test_concurrent)
{
    MemoryPool memory_pool{32};

    std::array<std::atomic<uint8_t *>, N> handles = {};

    ASSERT_TRUE(std::all_of(handles.begin(), handles.end(), [](auto const &x) {
        return x.load() == nullptr;
    }));

    std::vector<std::thread> alloc_threads;
    std::vector<std::thread> dealloc_threads;
    for (size_t i = 0; i < N; ++i) {
        alloc_threads.emplace_back([&memory_pool, &handles, i] {
            handles[i].store(memory_pool.alloc());
        });
        dealloc_threads.emplace_back([&memory_pool, &handles, i] {
            uint8_t *m = handles[i].load();
            while (!m) {
                std::this_thread::yield();
                m = handles[i].load();
            }
            memory_pool.dealloc(m);
        });
    }

    for (size_t i = 0; i < N; ++i) {
        alloc_threads.at(i).join();
        dealloc_threads.at(i).join();
    }

    ASSERT_TRUE(memory_pool.debug_check_uniqueness_invariant());
}

TEST(MonadVmMemoryPool, stress_test_in_steps)
{
    MemoryPool memory_pool{32};

    std::array<std::atomic<uint8_t *>, N> handles = {};

    ASSERT_TRUE(std::all_of(handles.begin(), handles.end(), [](auto const &x) {
        return x.load() == nullptr;
    }));

    std::vector<std::thread> alloc_threads;
    for (size_t i = 0; i < N; ++i) {
        alloc_threads.emplace_back([&memory_pool, &handles, i] {
            uint8_t *m = memory_pool.alloc();
            ASSERT_TRUE(
                std::all_of(m, m + 32, [](uint8_t const x) { return x == 0; }));
            handles[i].store(m);
        });
    }

    for (size_t i = 0; i < N; ++i) {
        alloc_threads.at(i).join();
    }

    ASSERT_EQ(memory_pool.debug_get_cache_size(), 0);

    std::vector<std::thread> dealloc_threads;
    for (size_t i = 0; i < N; ++i) {
        dealloc_threads.emplace_back([&memory_pool, &handles, i] {
            uint8_t *m = handles[i].load();
            while (!m) {
                std::this_thread::yield();
                m = handles[i].load();
            }
            memory_pool.dealloc(m);
        });
    }

    for (size_t i = 0; i < N; ++i) {
        dealloc_threads.at(i).join();
    }

    ASSERT_EQ(memory_pool.debug_get_cache_size(), N);
    ASSERT_TRUE(memory_pool.debug_check_uniqueness_invariant());
}
