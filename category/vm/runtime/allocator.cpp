#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/cached_allocator.hpp>

namespace monad::vm::runtime
{
    thread_local CachedAllocatorList EvmStackAllocatorMeta::cache_list;
    thread_local CachedAllocatorList EvmMemoryAllocatorMeta::cache_list;
}
