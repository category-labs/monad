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

#include <category/core/runtime/uint256.hpp>
#include <category/core/thread_local.h>
#include <category/vm/runtime/cached_allocator.hpp>

#include <cstddef>

namespace monad::vm::runtime
{
    struct EvmStackAllocatorMeta
    {
        using base_type = uint256_t;
        // 1024 EVM stack slots plus one. The interpreter keeps its empty-stack
        // pointer one slot below the first element, and that slot has to be
        // part of the array for the pointer arithmetic to be defined. Native
        // code uses slots [0, 1024) and never touches the extra one.
        static constexpr size_t size = 1024 + 1;
        static constexpr size_t alignment = 32;
        static MONAD_THREAD_LOCAL CachedAllocatorList cache_list;
    };

    using EvmStackAllocator = CachedAllocator<EvmStackAllocatorMeta>;
}
