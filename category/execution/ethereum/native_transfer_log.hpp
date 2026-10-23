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
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/commands/call_trace.hpp>
#include <category/execution/ethereum/trace/trace_context.hpp>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

class State;
class TxTraceContext;
struct CallTracerBase;

// Sender for the EIP-7002/EIP-7251 system calls; emitter for EIP-7708's logs.
inline constexpr Address ETH_SYSTEM_ADDRESS =
    0xfffffffffffffffffffffffffffffffffffffffe_address;

// ERC-7528
inline constexpr Address SIMULATE_NATIVE_TOKEN_LOG_ADDRESS =
    0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_address;

namespace detail
{
    inline Receipt::Log make_native_transfer_log(
        Address const &log_address, Address const &from, Address const &to,
        uint256_t const &value)
    {
        static constexpr bytes32_t signature =
            abi_encode_event_signature("Transfer(address,address,uint256)");
        static_assert(
            signature ==
            bytes32_from_hex("ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a"
                             "11628f55a4df523b3ef"));

        return EventBuilder(log_address, signature)
            .add_topic(abi_encode_address(from))
            .add_topic(abi_encode_address(to))
            .add_data(abi_encode_uint(u256_be{value}))
            .build();
    }
}

template <Traits traits>
void emit_native_transfer_logs(
    State &state, TxTraceContext const &trace_ctx, Address const &from,
    Address const &to, uint256_t const &value)
{
    if constexpr (!traits::eip_7708_active()) {
        if (MONAD_LIKELY(trace_ctx.size() == 0)) {
            return;
        }
    }

    if (MONAD_LIKELY(value == 0 || from == to)) {
        return;
    }

    if constexpr (traits::eip_7708_active()) {
        // Canonical logs must not depend on the tracing configuration.
        auto const event = detail::make_native_transfer_log(
            ETH_SYSTEM_ADDRESS, from, to, value);
        state.store_log(event);
        trace::emit<trace::Log>(trace_ctx, event);
    }
    else {
        trace::emit<trace::NativeTransfer>(
            trace_ctx,
            state,
            SIMULATE_NATIVE_TOKEN_LOG_ADDRESS,
            from,
            to,
            value);
    }
}

MONAD_NAMESPACE_END
