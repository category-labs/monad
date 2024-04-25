#include <monad/mem/huge_mem.h>

#include <monad/core/assert.h>
#include <monad/core/bit_util.h>

#include <linux/mman.h>
#include <sys/mman.h>

/**
 * TODO
 * - mbind (same numa node)
 */
void huge_mem_alloc(huge_mem_t *const mem, size_t const size)
{
    MONAD_ASSERT(mem->size == 0);
    MONAD_ASSERT(mem->data == nullptr);
    MONAD_ASSERT(size > 0);
    mem->size = bit_round_up(size, MAP_HUGE_2MB >> MAP_HUGE_SHIFT);
    mem->data = mmap(
        nullptr,
        mem->size,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB | MAP_HUGE_2MB,
        -1,
        0);
    MONAD_ASSERT(mem->data != MAP_FAILED);
    MONAD_ASSERT(!mlock(mem->data, mem->size));
}

void huge_mem_free(huge_mem_t *const mem)
{
    MONAD_ASSERT(mem->size);
    MONAD_ASSERT(mem->data);
    MONAD_ASSERT(!munlock(mem->data, mem->size));
    MONAD_ASSERT(!munmap(mem->data, mem->size));
    mem->size = 0;
    mem->data = nullptr;
}
