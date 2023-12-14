#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
struct EvmcHost;

class State;

void transfer_balances(
    State &, evmc_message const &, Address const &to) noexcept;

evmc_result transfer_call_balances(State &, evmc_message const &);

template <evmc_revision rev>
evmc::Result
deploy_contract_code(State &, Address const &, evmc::Result) noexcept;

template <evmc_revision rev>
evmc::Result create_contract_account(
    EvmcHost<rev> *, State &, evmc_message const &) noexcept;

template <evmc_revision rev>
evmc::Result call_evm(EvmcHost<rev> *, State &, evmc_message const &) noexcept;

MONAD_NAMESPACE_END
