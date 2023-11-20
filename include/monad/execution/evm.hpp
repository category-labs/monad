#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <tl/expected.hpp>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
struct EvmcHost;

struct State;

using result_t = tl::expected<void, evmc_result>;

result_t check_sender_balance(State &, evmc_message const &) noexcept;

void transfer_balances(
    State &, evmc_message const &, address_t const &to) noexcept;

evmc_result transfer_call_balances(State &, evmc_message const &);

template <evmc_revision rev>
evmc::Result
deploy_contract_code(State &, address_t const &, evmc::Result) noexcept;

template <evmc_revision rev>
evmc::Result create_contract_account(
    EvmcHost<rev> *, State &, evmc_message const &) noexcept;

template <evmc_revision rev>
evmc::Result call_evm(EvmcHost<rev> *, State &, evmc_message const &) noexcept;

MONAD_NAMESPACE_END
