#pragma once

#include <monad/config.hpp>

#include <cstddef>

typedef struct mi_heap_s mi_heap_t;

MONAD_NAMESPACE_BEGIN

/**
 * mimalloc allocator for use in boost object pool
 */
class PoolAllocator
{
    mi_heap_t *const heap_;

public:
    typedef size_t size_type;
    typedef ptrdiff_t difference_type;

    PoolAllocator(mi_heap_t * = nullptr);

    char *malloc(size_type);

    static void free(char *);
};

MONAD_NAMESPACE_END
