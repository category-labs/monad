#pragma once

#include <monad/config.hpp>

#include <cstddef>

MONAD_NAMESPACE_BEGIN

class HugeMem final
{
    size_t const size_;
    void *const mem_;

public:
    HugeMem(size_t);
    ~HugeMem();

    [[gnu::always_inline]] size_t getSize() const { return size_; }

    [[gnu::always_inline]] void *getMem() const { return mem_; }
};

MONAD_NAMESPACE_END
