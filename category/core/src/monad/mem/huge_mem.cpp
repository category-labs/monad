#include <monad/mem/huge_mem.hpp>

#include <monad/config.hpp>

#include <monad/core/assert.h>

#include <linux/mman.h>
#include <sys/mman.h>

#include <cstddef>

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

HugeMem::HugeMem(size_t const size)
    : size_{[size] {
        MONAD_ASSERT(size > 0);
        return round_up(size, MAP_HUGE_2MB >> MAP_HUGE_SHIFT);
    }()}
    , data_{[this] {
        void *const data = mmap(
            nullptr,
            size_,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB | MAP_HUGE_2MB,
            -1,
            0);
        MONAD_ASSERT(data != MAP_FAILED);
        return static_cast<unsigned char *>(data);
    }()}
{
    /**
     * TODO
     * - mbind (same numa node)
     */

    MONAD_ASSERT(!mlock(data_, size_));
}

HugeMem::~HugeMem()
{
    if (size_ > 0) {
        MONAD_ASSERT(!munlock(data_, size_));
        MONAD_ASSERT(!munmap(data_, size_));
    }
}

MONAD_NAMESPACE_END
