#pragma once

#include <monad/mpt/config.hpp>
#include <monad/mpt/update.hpp>

#include <monad/mem/pool_allocator.hpp>

#include <boost/pool/object_pool.hpp>

typedef struct mi_heap_s mi_heap_t;

MONAD_MPT_NAMESPACE_BEGIN

class Mem
{
    mi_heap_t *const heap_;
    boost::object_pool<Update, PoolAllocator> update_pool_;

public:
    Mem(mi_heap_t * = nullptr);

    mi_heap_t *get_heap() const noexcept
    {
        return heap_;
    }

    auto &get_update_pool() const noexcept
    {
        return update_pool_;
    }
};

MONAD_MPT_NAMESPACE_END
