#pragma once

#include <monad/vm/runtime/cached_allocator.hpp>

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
