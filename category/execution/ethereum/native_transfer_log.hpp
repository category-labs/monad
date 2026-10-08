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

#pragma once

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

class State;
struct CallTracerBase;

// Sender for the EIP-7002/EIP-7251 system calls; emitter for EIP-7708's logs.
inline constexpr Address ETH_SYSTEM_ADDRESS =
    0xfffffffffffffffffffffffffffffffffffffffe_address;

// ERC-7528
inline constexpr Address SIMULATE_NATIVE_TOKEN_LOG_ADDRESS =
    0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_address;

namespace detail
{
    void emit_native_transfer_log(
        State &, CallTracerBase &, Address const &log_address,
        Address const &from, Address const &to, uint256_t const &value);
}

template <Traits traits>
void emit_native_transfer_logs(
    State &state, CallTracerBase &call_tracer, Address const &from,
    Address const &to, uint256_t const &value, bool const log_native_transfers)
{
    if constexpr (!traits::eip_7708_active()) {
        if (MONAD_LIKELY(!log_native_transfers)) {
            return;
        }
    }

    if (MONAD_LIKELY(value == 0 || from == to)) {
        return;
    }

    // Geth emits eth_simulate transfers before EIP-7708 for calls and
    // creates (implementation detail; unspecified).
    if (log_native_transfers) {
        detail::emit_native_transfer_log(
            state,
            call_tracer,
            SIMULATE_NATIVE_TOKEN_LOG_ADDRESS,
            from,
            to,
            value);
    }

    if constexpr (traits::eip_7708_active()) {
        detail::emit_native_transfer_log(
            state, call_tracer, ETH_SYSTEM_ADDRESS, from, to, value);
    }
}

MONAD_NAMESPACE_END
