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

#include <category/vm/runtime/cached_allocator.hpp>

namespace monad::vm::runtime
{
    struct EvmStackAllocatorMeta
    {
        using base_type = uint256_t;
        static constexpr size_t size = 1024;
        static constexpr size_t alignment = 32;
        static thread_local CachedAllocatorList cache_list;
    };

    struct EvmMemoryAllocatorMeta
    {
        using base_type = uint8_t;
        static constexpr size_t size = 4096;
        static constexpr size_t alignment = 1;
        static thread_local CachedAllocatorList cache_list;
    };

    using EvmStackAllocator = CachedAllocator<EvmStackAllocatorMeta>;
    using EvmMemoryAllocator = CachedAllocator<EvmMemoryAllocatorMeta>;
}
