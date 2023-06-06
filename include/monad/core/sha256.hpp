#pragma once

#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

namespace crypto
{
    void sha256(uint8_t hash[32], const uint8_t *input, size_t len);
}

MONAD_NAMESPACE_END
