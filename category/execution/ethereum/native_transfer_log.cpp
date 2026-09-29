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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/native_transfer_log.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <utility>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    void emit_native_transfer_log(
        State &state, CallTracerBase &call_tracer, Address const &log_address,
        Address const &from, Address const &to, uint256_t const &value)
    {
        static constexpr bytes32_t signature =
            abi_encode_event_signature("Transfer(address,address,uint256)");
        static_assert(
            signature ==
            bytes32_from_hex("ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a"
                             "11628f55a4df523b3ef"));

        auto event = EventBuilder(log_address, signature)
                         .add_topic(abi_encode_address(from))
                         .add_topic(abi_encode_address(to))
                         .add_data(abi_encode_uint(u256_be{value}))
                         .build();

        state.store_log(event);
        call_tracer.on_log(std::move(event));
    }
}

MONAD_NAMESPACE_END
