#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

MONAD_NAMESPACE_END
