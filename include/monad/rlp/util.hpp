#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

inline byte_string_view zeroless_view(byte_string_view const s)
{
    auto b = s.begin();
    auto const e = s.end();
    while (b < e && *b == 0) {
        ++b;
    }
    return {b, e};
}

inline byte_string to_big_compact(unsigned_integral auto n)
{
    n = intx::to_big_endian(n);
    return byte_string(
        zeroless_view({reinterpret_cast<unsigned char *>(&n), sizeof(n)}));
}

MONAD_NAMESPACE_END
