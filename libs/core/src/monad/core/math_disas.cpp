#include <monad/config.hpp>

#include <monad/core/math.hpp>

#include <cstddef>

MONAD_NAMESPACE_BEGIN

size_t round_up_disas(size_t const x, size_t const y)
{
    return round_up(x, y);
}

MONAD_NAMESPACE_END
