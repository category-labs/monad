#include <monad/mpt/mem.hpp>

#include <monad/mpt/config.hpp>

#include <mimalloc.h>

MONAD_MPT_NAMESPACE_BEGIN

Mem::Mem(mi_heap_t *const heap)
    : heap_{heap ? heap : mi_heap_get_default()}
    , update_pool_{1UL << 16}
{
}

MONAD_MPT_NAMESPACE_END
