#include <monad/mem/cpool.h>

#include <stdint.h>

CPOOL_DEFINE(21)

cpool_21_t *pool_init_disas(unsigned char *const mem)
{
    return cpool_init21(mem);
}

unsigned char *pool_ptr_disas(cpool_21_t *const p, uint32_t const i)
{
    return cpool_ptr21(p, i);
}

uint32_t pool_reserve_disas(cpool_21_t *const p, uint32_t const n)
{
    return cpool_reserve21(p, n);
}

void pool_advance_disas(cpool_21_t *const p, uint32_t const n)
{
    cpool_advance21(p, n);
}

bool pool_valid_disas(cpool_21_t *const p, uint32_t const i)
{
    return cpool_valid21(p, i);
}
