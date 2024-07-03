#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/int.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <oneapi/tbb/concurrent_hash_map.h>
#pragma GCC diagnostic pop

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class IntrinsicGasBuffer
{
public:
    static constexpr auto N = 10;

private:
    using Map = oneapi::tbb::concurrent_hash_map<Address, uint256_t>;

    uint64_t n_{0};
    Map b_[N];

public:
    void set_block_number(uint64_t const n)
    {
        MONAD_ASSERT(!n_ || n == n_ + 1);
        b_[n % N].clear();
        n_ = n;
    }

    void add(Address const &a, uint256_t const g)
    {
        Map::accessor it;
        bool const inserted = b_[n_ % N].insert(it, {a, g});
        if (!inserted) {
            it->second += g;
        }
    }

    uint256_t sum(Address const &a) const
    {
        uint256_t sum = 0;
        for (auto const &m : b_) {
            Map::const_accessor it;
            bool const found = m.find(it, a);
            if (found) {
                sum += it->second;
            }
        }
        return sum;
    }
};

static_assert(sizeof(IntrinsicGasBuffer) == 5768);
static_assert(alignof(IntrinsicGasBuffer) == 8);

MONAD_NAMESPACE_END
