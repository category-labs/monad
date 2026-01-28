// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits, typename Contract, Address contract_address>
std::optional<evmc::Result> check_call_monad_precompile(
    State &state, CallTracerBase &call_tracer, evmc_message const &msg)
{

    if (msg.code_address != contract_address) {
        return std::nullopt;
    }

    if (MONAD_UNLIKELY(msg.kind != EVMC_CALL) || (msg.flags != 0)) {
        return evmc::Result{evmc_status_code::EVMC_REJECTED};
    }

    byte_string_view input{msg.input_data, msg.input_size};
    auto const [method, cost] =
        Contract::template precompile_dispatch<traits>(input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    Contract contract = Contract{state, call_tracer};
    auto const res = (contract.*method)(input, msg.sender, msg.value);
    if (MONAD_LIKELY(res.has_value())) {
        int64_t const gas_left = msg.gas - static_cast<int64_t>(cost);
        int64_t const gas_refund = 0;
        return evmc::Result(
            EVMC_SUCCESS,
            gas_left,
            gas_refund,
            res.value().data(),
            res.value().size());
    }
    return evmc::Result(
        EVMC_REVERT,
        0 /* gas left */,
        0 /* gas refund */,
        reinterpret_cast<uint8_t const *>(res.error().message().data()),
        res.error().message().size());
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
bool is_precompile(Address const &address)
{
    // Note that if new Monad-specific precompiles are added, identifying them
    // as a precompile should be gated behind the revision they were activated
    // in.
    return is_eth_precompile<traits>(address) ||
           (address == staking::STAKING_CA) ||
           (traits::monad_rev() >= MONAD_NEXT &&
            address == RESERVE_BALANCE_CA); // TODO(dhil): FIXME revision
}

EXPLICIT_MONAD_TRAITS(is_precompile);

template <Traits traits>
std::optional<evmc::Result> check_call_precompile(
    State &state, CallTracerBase &call_tracer, evmc_message const &msg)
{
    if (auto maybe_result = check_call_eth_precompile<traits>(msg)) {
        return maybe_result;
    }

#define CASE(cond, contract, addr)                                             \
    do {                                                                       \
        if constexpr ((cond)) {                                                \
            if (auto maybe_result =                                            \
                    check_call_monad_precompile<traits, contract, addr>(       \
                        state, call_tracer, msg)) {                            \
                return maybe_result;                                           \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false);

    CASE(
        traits::monad_rev() >= MONAD_FOUR,
        staking::StakingContract,
        staking::STAKING_CA);

    CASE(
        traits::monad_rev() >= MONAD_NEXT, // TODO(dhil): FIXME revision
        ReserveBalanceContract,
        RESERVE_BALANCE_CA);

    return std::nullopt;

#undef CASE
}

EXPLICIT_MONAD_TRAITS(check_call_precompile);

MONAD_NAMESPACE_END
