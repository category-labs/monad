#pragma once

#include <monad/config.hpp>

#include <cstddef>

MONAD_NAMESPACE_BEGIN

class HugeMem
{
protected:
    size_t const size_;
    void *const mem_;

public:
    HugeMem(size_t);
    ~HugeMem();
};

MONAD_NAMESPACE_END
