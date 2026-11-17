// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/domain/ale/application_encryption_contract.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits, typename Contract, Address contract_address>
std::optional<vm::Result> check_call_domain_precompile(
    State &state, CallTracerBase &call_tracer, vm::Message const &msg,
    bool const log_native_transfers,
    ChainContext<traits> const *const chain_context)
{
    if (msg.code_address != contract_address) {
        return std::nullopt;
    }

    if (MONAD_UNLIKELY(
            chain_context == nullptr || !chain_context->private_domain ||
            chain_context->encryption_context == nullptr)) {
        return vm::Result{CallStatus::Rejected};
    }
    if (MONAD_UNLIKELY(msg.kind != vm::CallKind::Call) || (msg.flags != 0)) {
        return vm::Result{CallStatus::Rejected};
    }

    byte_string_view input{msg.input_data, msg.input_size};
    auto const [method, cost] =
        Contract::template precompile_dispatch<traits>(input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return vm::Result{CallStatus::OutOfGas};
    }

    Contract contract{
        state,
        call_tracer,
        *chain_context->encryption_context,
        log_native_transfers};
    auto const res = (contract.*method)(input, msg.sender, msg.value);
    if (MONAD_LIKELY(res.has_value())) {
        int64_t const gas_left = msg.gas - static_cast<int64_t>(cost);
        int64_t const gas_refund = 0;
        return vm::Result(
            CallStatus::Success,
            gas_left,
            gas_refund,
            res.value().data(),
            res.value().size());
    }
    return vm::Result(
        CallStatus::Revert,
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
    return is_eth_precompile<traits>(address) ||
           (traits::ale_active() && address == ALE_CA);
}

EXPLICIT_MONAD_TRAITS(is_precompile);

template <Traits traits>
std::optional<vm::Result> check_call_precompile(
    State &state, CallTracerBase &call_tracer, vm::Message const &msg,
    bool const log_native_transfers,
    ChainContext<traits> const *const chain_context)
{
    if (auto maybe_result = check_call_eth_precompile<traits>(msg)) {
        return maybe_result;
    }

#define CASE(cond, contract, addr)                                             \
    do {                                                                       \
        if constexpr ((cond)) {                                                \
            if (auto maybe_result =                                            \
                    check_call_domain_precompile<traits, contract, addr>(      \
                        state,                                                 \
                        call_tracer,                                           \
                        msg,                                                   \
                        log_native_transfers,                                  \
                        chain_context)) {                                      \
                return maybe_result;                                           \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false);

    CASE(traits::ale_active(), ApplicationEncryptionContract, ALE_CA);

    return std::nullopt;

#undef CASE
}

EXPLICIT_MONAD_TRAITS(check_call_precompile);

MONAD_NAMESPACE_END
