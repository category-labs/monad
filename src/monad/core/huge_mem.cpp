#include <monad/core/huge_mem.hpp>

#include <monad/core/assert.h>

#include <linux/mman.h>
#include <sys/mman.h>

MONAD_NAMESPACE_BEGIN

namespace
{
    size_t round_up(size_t size, unsigned const bits)
    {
        size_t const mask = (1UL << bits) - 1;
        bool const rem = size & mask;
        size >>= bits;
        size += rem;
        size <<= bits;
        return size;
    }
}

/**
 * TODO
 * - mbind (same numa node)
 * - mlock (no paging)
 */
HugeMem::HugeMem(size_t const size)
    : size_{round_up(size, 21)}
    , mem_{mmap(
          nullptr, size_, PROT_READ | PROT_WRITE,
          MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB | MAP_HUGE_2MB, -1, 0)}
{
    MONAD_ASSERT(mem_ != MAP_FAILED);
}

HugeMem::~HugeMem()
{
    int const munmap_result = munmap(mem_, size_);
    MONAD_ASSERT(!munmap_result);
}

MONAD_NAMESPACE_END
