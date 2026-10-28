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

#include <category/core/thread_local.h>
#include <category/vm/runtime/cached_allocator.hpp>

namespace monad::vm::runtime
{
    struct EvmStackAllocatorMeta
    {
        using base_type = uint256_t;
#if defined(MONAD_ZKVM_ZISK)
        // One slot past the 1024 the EVM can fill: the interpreter's SWAP1,
        // and its pair with SWAP2, copy a word to the slot above the top,
        // then move the words down one slot over it (execute.cpp,
        // swap1_then), so that slot must exist when the stack is full. It
        // holds nothing between two instructions, and the stack's limit
        // stays at 1024.
        static constexpr size_t size = 1025;
#else
        static constexpr size_t size = 1024;
#endif
        static constexpr size_t alignment = 32;
        static MONAD_THREAD_LOCAL CachedAllocatorList cache_list;
    };

    using EvmStackAllocator = CachedAllocator<EvmStackAllocatorMeta>;
}
