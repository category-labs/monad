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

MONAD_NAMESPACE_BEGIN

static constexpr auto RESERVE_BALANCE_CA = Address{0x1001};
static constexpr uint256_t DEFAULT_RESERVE_BALANCE_WEI =
    10 * uint256_t{1'000'000'000'000'000'000};

class ReserveBalanceContract
{
    State &state_;

public:
    explicit ReserveBalanceContract(State &state);

    u256_be get(Address const &);

    void set(Address const &, u256_be const &);

private:
    /////////////
    // Events //
    /////////////

    // event ReserveBalanceChanged(
    //     address indexed account,
    //     uint256         oldValue,
    //     uint256         newValue);
    void emit_reserve_balance_changed_event(
        Address const &, u256_be const &, u256_be const &);

public:
    using PrecompileFunc = Result<byte_string> (ReserveBalanceContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    /////////////////
    // Precompiles //
    /////////////////
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Result<byte_string> precompile_get(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    Result<byte_string> precompile_set(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    Result<byte_string> precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
};

MONAD_NAMESPACE_END
