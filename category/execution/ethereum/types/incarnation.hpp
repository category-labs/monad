#pragma once

#include <category/core/config.hpp>

#include <bit>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

class Incarnation
{
    uint64_t block_ : 40;
    uint64_t tx_ : 24;

public:
    static constexpr uint64_t LAST_TX = (1UL << 24) - 1;

    explicit Incarnation(uint64_t const block, uint64_t const tx)
        : block_{block & 0xFFFFFFFFFF}
        , tx_{tx & 0xFFFFFF}
    {
    }

    uint64_t get_block() const
    {
        return block_;
    }

    uint64_t get_tx() const
    {
        return tx_;
    }

    uint64_t to_int() const
    {
        return std::bit_cast<uint64_t>(*this);
    }

    static Incarnation from_int(uint64_t const incarnation)
    {
        return std::bit_cast<Incarnation>(incarnation);
    }
};

static_assert(sizeof(Incarnation) == 8);

inline bool operator==(Incarnation const i1, Incarnation const i2)
{
    return i1.to_int() == i2.to_int();
}

MONAD_NAMESPACE_END
