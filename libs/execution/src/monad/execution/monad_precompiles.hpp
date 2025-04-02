#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

class State;

std::optional<evmc::Result>
monad_check_call_precompile(State &, evmc_message const &);

MONAD_NAMESPACE_END
