#pragma once

#include <monad/io/config.hpp>

MONAD_IO_NAMESPACE_BEGIN

class Buffers;

class BufferPool
{
    unsigned char *next_;

public:
    BufferPool(Buffers const &, bool is_read);

    [[gnu::always_inline]] [[nodiscard]] bool empty() const noexcept
    {
        return next_ == nullptr;
    }

    [[gnu::always_inline]] unsigned char *alloc()
    {
        unsigned char *const next = next_;
        if (next) {
            next_ = *reinterpret_cast<unsigned char **>(next);
        }
        return next;
    }

    [[gnu::always_inline]] void release(unsigned char *const next)
    {
        *reinterpret_cast<unsigned char **>(next) = next_;
        next_ = next;
    }
};

static_assert(sizeof(BufferPool) == 8);
static_assert(alignof(BufferPool) == 8);

MONAD_IO_NAMESPACE_END
