#pragma once

#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>

#include <cstdint>

MONAD_EVM_NAMESPACE_BEGIN

constexpr auto word_size = sizeof(uint256_t);
static_assert(word_size == 32);

// returns in units of words
constexpr size_t round_up_bytes_to_words(size_t const n) noexcept
{
    return (n + word_size - 1) / word_size;
}

MONAD_EVM_NAMESPACE_END
