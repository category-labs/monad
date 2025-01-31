#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
struct EvmcHost;

class State;

template <evmc_revision rev>
evmc::Result
deploy_contract_code(State &, Address const &, evmc::Result) noexcept;

template <evmc_revision rev>
evmc::Result create(EvmcHost<rev> *, State &, evmc_message const &) noexcept;

template <evmc_revision rev>
evmc::Result call(EvmcHost<rev> *, State &, evmc_message const &) noexcept;

MONAD_NAMESPACE_END
