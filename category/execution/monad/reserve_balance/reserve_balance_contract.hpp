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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

static constexpr Address RESERVE_BALANCE_CA = Address{0x1001};

class ReserveBalanceContract
{
    State &state_;
    // TODO(dhil): Remove annotation once used in event emission.
    [[maybe_unused]] CallTracerBase &call_tracer_;

public:
    ReserveBalanceContract(State &state, CallTracerBase &tracer);

    using PrecompileFunc = Result<byte_string> (ReserveBalanceContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    //
    // Precompile methods
    //
    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Result<byte_string> precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
};

MONAD_NAMESPACE_END
