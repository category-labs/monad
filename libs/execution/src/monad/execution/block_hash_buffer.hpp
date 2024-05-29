#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer
{
    static constexpr unsigned N = 256;

    bytes32_t b_[N];
    uint64_t n_;

public:
    BlockHashBuffer();

    void set(uint64_t const n, bytes32_t const &h)
    {
        MONAD_ASSERT(!n_ || n == n_);
        b_[n % N] = h;
        n_ = n + 1;
    }

    bytes32_t const &get(uint64_t const n) const
    {
        MONAD_ASSERT(n < n_ && n + N >= n_);
        return b_[n % N];
    }

    void to_prev()
    {
        MONAD_DEBUG_ASSERT(n_ >= 1);
        n_--;
        b_[n_ % N] = NULL_HASH;
    }
};

MONAD_NAMESPACE_END
