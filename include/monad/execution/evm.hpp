#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/evm/config.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_EVM_NAMESPACE_BEGIN

struct CallParameters;
enum class Status;
class SystemState;

MONAD_EVM_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
struct EvmcHost;

class State;

evmc::Result transfer_call_balances(State &, evmc_message const &);
evm::Status
transfer_call_balances(evm::CallParameters const &, evm::SystemState &);

template <evmc_revision rev>
evmc::Result
deploy_contract_code(State &, Address const &, evmc::Result) noexcept;

template <evmc_revision rev>
evmc::Result create_contract_account(
    EvmcHost<rev> *, State &, evmc_message const &) noexcept;

template <evmc_revision rev>
evmc::Result call(EvmcHost<rev> *, State &, evmc_message const &) noexcept;

MONAD_NAMESPACE_END
