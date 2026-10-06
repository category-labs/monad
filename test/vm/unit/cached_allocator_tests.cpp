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

#include <category/core/asan.h>
#include <category/vm/runtime/allocator.hpp>

#include <gtest/gtest.h>

#include <cstddef>

using namespace monad::vm::runtime;

TEST(CachedAllocator, owner_keeps_its_allocator_cache_limit)
{
    EvmStackAllocator const allocator;
    allocator.debug_clear_cache();
    auto cached = EvmStackAllocator{EvmStackAllocator::alloc_size}.allocate();
    auto uncached = EvmStackAllocator{0}.allocate();
    uncached.reset();
    EXPECT_TRUE(EvmStackAllocatorMeta::cache_list.empty());
    cached.reset();
    EXPECT_EQ(EvmStackAllocatorMeta::cache_list.size(), 1);
    allocator.debug_clear_cache();
}

#ifdef MONAD_HAVE_ASAN
TEST(CachedAllocator, free_cached_poisons_block)
{
    EvmStackAllocator const allocator;
    std::byte *const p = allocator.aligned_alloc_cached();
    allocator.free_cached(p);
    ASSERT_TRUE(__asan_address_is_poisoned(p));
    ASSERT_TRUE(
        __asan_address_is_poisoned(p + EvmStackAllocator::alloc_size - 1));
    ASSERT_EQ(allocator.aligned_alloc_cached(), p);
    ASSERT_EQ(
        __asan_region_is_poisoned(p, EvmStackAllocator::alloc_size), nullptr);
    allocator.free_cached(p);
}
#endif
