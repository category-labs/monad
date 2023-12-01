#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using Address = ::evmc::address;

static_assert(sizeof(Address) == 20);
static_assert(alignof(Address) == 1);

MONAD_NAMESPACE_END
