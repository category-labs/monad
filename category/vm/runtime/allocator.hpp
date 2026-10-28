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
        static constexpr size_t max_stack_height = 1024;
#if defined(MONAD_ZKVM_ZISK)
        // SWAP1 uses the slot above the top as scratch, even on a full stack.
        // This extra allocation does not raise the EVM stack limit.
        static constexpr size_t size = max_stack_height + 1;
#else
        static constexpr size_t size = max_stack_height;
#endif
        static constexpr size_t alignment = 32;
        static MONAD_THREAD_LOCAL CachedAllocatorList cache_list;
    };

    using EvmStackAllocator = CachedAllocator<EvmStackAllocatorMeta>;
}
