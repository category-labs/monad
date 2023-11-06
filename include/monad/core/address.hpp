#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using address_t = ::evmc::address;

static_assert(sizeof(address_t) == 20);
static_assert(alignof(address_t) == 1);

MONAD_NAMESPACE_END
