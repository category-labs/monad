#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

using namespace evmc::literals;
inline constexpr bytes32_t NULL_HASH{0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_bytes32};

// Root hash of an empty trie
inline constexpr bytes32_t NULL_ROOT{0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32};

MONAD_NAMESPACE_END
