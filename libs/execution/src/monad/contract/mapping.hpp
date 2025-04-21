#pragma once

#include <monad/config.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/bytes.hpp>

#include <type_traits>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

template <typename... Args>
    requires(std::is_trivially_copyable_v<Args> && ...)
bytes32_t mapping(Args const &...args)
{
    blake3_hasher ctx;
    hash256 output;
    blake3_hasher_init(&ctx);

    ([&] { blake3_hasher_update(&ctx, &args, sizeof(args)); }(), ...);

    blake3_hasher_finalize(&ctx, output.bytes, BLAKE3_OUT_LEN);
    return std::bit_cast<bytes32_t>(output);
}

MONAD_NAMESPACE_END
