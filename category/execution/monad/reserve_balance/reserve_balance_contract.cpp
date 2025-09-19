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

#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_error.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

////////////////////////
// Function Selectors //
////////////////////////

struct PrecompileSelector
{
    static constexpr uint32_t GET = abi_encode_selector("get()");
    static constexpr uint32_t SET = abi_encode_selector("set(uint256)");
};

static_assert(PrecompileSelector::GET == 0x6d4ce63c);
static_assert(PrecompileSelector::SET == 0x60fe47b1);

//////////////
// Gas Costs //
///////////////

// The gas for the reserve balance precompile are determined by sloads, sstores
// and events. The operations are given as the following:
//
// operations = [
//   number_of_cold_sloads,
//   number_of_warm_nonzero_sstores,
//   number_of_events,
//   ]
//
// The gas cost is calculated as:
// gas = COLD_SLOAD_COST * operations[0] +
//       WARM_NONZERO_SSTORE_COST * operations[1] +
//       EVENT_COST * operations[2]
//

constexpr uint64_t COLD_SLOAD = 8100;
constexpr uint64_t WARM_SSTORE_NONZERO = 2900;
constexpr uint64_t EVENT_COSTS = 4275;

struct OpCount
{
    uint64_t cold_sloads;
    uint64_t warm_sstore_nonzero;
    uint64_t events;
};

constexpr uint64_t compute_costs(OpCount const &ops) noexcept
{
    return COLD_SLOAD * ops.cold_sloads +
           WARM_SSTORE_NONZERO * ops.warm_sstore_nonzero +
           EVENT_COSTS * ops.events;
}

constexpr uint64_t GET_OP_COST = compute_costs({
    .cold_sloads = 1,
    .warm_sstore_nonzero = 0,
    .events = 0,
});

constexpr uint64_t SET_OP_COST = compute_costs({
    .cold_sloads = 1,
    .warm_sstore_nonzero = 1,
    .events = 1,
});

constexpr uint64_t FALLBACK_COST = 40'000;

static_assert(GET_OP_COST == 8100);
static_assert(SET_OP_COST == 15275);

Result<void> function_not_payable(u256_be const &value)
{
    if (MONAD_UNLIKELY(!value.is_zero())) {
        return ReserveBalanceError::ValueNonZero;
    }

    return outcome::success();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

ReserveBalanceContract::ReserveBalanceContract(State &state)
    : state_{state}
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

u256_be ReserveBalanceContract::get(Address const &sender)
{
    auto const key = abi_encode_address(sender);
    auto const slot = StorageVariable<u256_be>{state_, RESERVE_BALANCE_CA, key};
    auto const value = slot.load_checked();
    return value.value_or(DEFAULT_RESERVE_BALANCE_WEI);
}

void ReserveBalanceContract::set(Address const &sender, u256_be const &value)
{
    auto const key = abi_encode_address(sender);
    auto slot = StorageVariable<u256_be>{state_, RESERVE_BALANCE_CA, key};

    auto const old_value = slot.load();
    auto const new_value =
        value.is_zero() ? DEFAULT_RESERVE_BALANCE_WEI : value;

    slot.store(new_value);
    emit_reserve_balance_changed_event(sender, old_value, new_value);
}

void ReserveBalanceContract::emit_reserve_balance_changed_event(
    Address const &sender, u256_be const &old_value, u256_be const &new_value)
{
    static constexpr auto signature = abi_encode_event_signature(
        "ReserveBalanceChanged(address,uint256,uint256)");
    static_assert(
        signature ==
        0xecbead9d902aef6900edfcf4e3ec205b52f4f59866d086bbf0d6388fc9b30d97_bytes32);

    auto const event = EventBuilder(RESERVE_BALANCE_CA, signature)
                           .add_topic(abi_encode_address(sender))
                           .add_data(abi_encode_uint(old_value))
                           .add_data(abi_encode_uint(new_value))
                           .build();
    state_.store_log(event);
}

std::pair<ReserveBalanceContract::PrecompileFunc, uint64_t>
ReserveBalanceContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case PrecompileSelector::GET:
        return {&ReserveBalanceContract::precompile_get, GET_OP_COST};
    case PrecompileSelector::SET:
        return {&ReserveBalanceContract::precompile_set, SET_OP_COST};
    default:
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }
}

Result<byte_string> ReserveBalanceContract::precompile_get(
    byte_string_view input, evmc_address const &sender,
    evmc_bytes32 const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(u256_be::from_bytes(msg_value)));

    if (MONAD_UNLIKELY(!input.empty())) {
        return ReserveBalanceError::InvalidInput;
    }

    auto const value = get(sender);
    return byte_string(abi_encode_uint(value));
}

Result<byte_string> ReserveBalanceContract::precompile_set(
    byte_string_view input, evmc_address const &sender,
    evmc_bytes32 const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(u256_be::from_bytes(msg_value)));

    BOOST_OUTCOME_TRY(auto const value, abi_decode_fixed<u256_be>(input));

    if (MONAD_UNLIKELY(!input.empty())) {
        return ReserveBalanceError::InvalidInput;
    }

    set(sender, value);
    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> ReserveBalanceContract::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return ReserveBalanceError::MethodNotSupported;
}

MONAD_NAMESPACE_END
