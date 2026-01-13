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

#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

static constexpr Address RESERVE_BALANCE_CA = Address{0x1001};
static constexpr uint256_t DEFAULT_RESERVE_BALANCE_WEI =
    10 * uint256_t{1'000'000'000'000'000'000};
static constexpr uint64_t DELAY_BLOCKS = 3; // k

// clang-format off
// Morally, this precompile is equivalent to the following Solidity contract:
//
// contract ReserveBalance {
//   uint256 private constant DEFAULT_RESERVE_BALANCE_WEI = 10'000'000'000'000'000'000; 
//   mapping (address => uint256) private reserveBalances_;
//
//   function update(uint256 newValue) external {
//     uint256 oldValue = reserveBalances_[msg.sender];
//
//     reserveBalances_[msg.sender] = newValue == 0 ?
//        DEFAULT_RESERVE_BALANCE_WEI : newValue;
//
//     emit ReserveBalanceChanged(msg.sender, oldValue, reserveBalances_[msg.sender]);
//   }
// }
// clang-format on
class ReserveBalanceContract
{
    State &state_;
    CallTracerBase &call_tracer_;

public:
    ReserveBalanceContract(State &state, CallTracerBase &tracer);

    Result<uint256_t> update(State &, Address const &, uint256_t const &);

private:
    //
    // Events
    //

    // event ReserveBalanceChanged(
    //     address indexed account,
    //     uint256         oldValue,
    //     uint256         newValue);
    void emit_reserve_balance_changed_event(
        bytes32_t const &, u256_be const &, u256_be const &);

public:
    using PrecompileFunc = Result<byte_string> (ReserveBalanceContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    //
    // Precompile methods
    //
    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Result<byte_string> precompile_update(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    Result<byte_string> precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
};

// Whereas the above class is intended for external Solidity code / smart
// contracts to interact with (i.e. update) reserve balances; the below class is
// intended for the Monad execution environment to interact (i.e. read) with
// reserve balances.
class ReserveBalanceView
{
    State &state_;

public:
    explicit ReserveBalanceView(State &);

    uint256_t get_delayed_urb(Address const &);
};

bool is_reconfiguring_transaction(Transaction const &);

MONAD_NAMESPACE_END
