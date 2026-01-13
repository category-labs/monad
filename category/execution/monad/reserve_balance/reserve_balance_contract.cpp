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
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

//
// ABI
//

static constexpr uint32_t UPDATE_SELECTOR =
    abi_encode_selector("update(uint256)");
static_assert(UPDATE_SELECTOR == 0x82ab890a);

//
// Gas Costs
//

// The gas for the reserve balance precompile are determined by sload, sstores
// and events. The gas cost is calculated as:
//
// gas = COLD_SLOAD_COST * number_of_cold_sloads +
//       WARM_NONZERO_SSTORE_COST * number_of_warm_nonzero_sstores +
//       EVENT_COST * number_of_events
//

constexpr uint64_t COLD_SLOAD_COST = 8100;
constexpr uint64_t WARM_SSTORE_NONZERO_COST = 2900;
constexpr uint64_t EVENT_COSTS = 4275;
constexpr uint64_t UPDATE_OP_COST =
    COLD_SLOAD_COST + WARM_SSTORE_NONZERO_COST + EVENT_COSTS;
constexpr uint64_t FALLBACK_COST = 40'000;

static_assert(UPDATE_OP_COST == 15275);

Result<void> function_not_payable(u256_be const &value)
{
    if (MONAD_UNLIKELY(!value.is_zero())) {
        return ReserveBalanceError::ValueNonZero;
    }

    return outcome::success();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bool is_reconfiguring_transaction(Transaction const &tx)
{
    if (tx.to == RESERVE_BALANCE_CA && tx.value == 0 &&
        tx.data.size() >= sizeof(uint32_t)) {
        unsigned char const *b =
            reinterpret_cast<uint8_t const *>(tx.data.data());
        uint32_t const selector = (uint32_t(b[0]) << 24) |
                                  (uint32_t(b[1]) << 16) |
                                  (uint32_t(b[2]) << 8) | (uint32_t(b[3]));
        return selector == UPDATE_SELECTOR;
    }
    return false;
}

ReserveBalanceContract::ReserveBalanceContract(
    State &state, CallTracerBase &tracer)
    : state_{state}
    , call_tracer_{tracer}
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

u256_be ReserveBalanceContract::update(
    State &state, bytes32_t const &sender, u256_be const &new_value)
{
    auto slot = StorageVariable<u256_be>{state, RESERVE_BALANCE_CA, sender};
    auto const old_value = slot.load_checked();
    slot.store(new_value);
    return old_value.value_or(u256_be{DEFAULT_RESERVE_BALANCE_WEI});
}

uint256_t ReserveBalanceContract::update(
    State &state, Address const &address, uint256_t const &new_value)
{
    auto const key = abi_encode_address(address);
    u256_be new_value_be{new_value};
    auto const old_value_be = update(state, key, new_value_be);
    return intx::be::load<uint256_t>(old_value_be.bytes);
}

void ReserveBalanceContract::emit_reserve_balance_changed_event(
    bytes32_t const &sender, u256_be const &old_value, u256_be const &new_value)
{
    static constexpr auto signature = abi_encode_event_signature(
        "ReserveBalanceChanged(address,uint256,uint256)");
    static_assert(
        signature ==
        0xecbead9d902aef6900edfcf4e3ec205b52f4f59866d086bbf0d6388fc9b30d97_bytes32);

    auto const event = EventBuilder(RESERVE_BALANCE_CA, signature)
                           .add_topic(sender)
                           .add_data(abi_encode_uint(old_value))
                           .add_data(abi_encode_uint(new_value))
                           .build();
    state_.store_log(event);
    call_tracer_.on_log(event);
}

template <Traits traits>
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
    case UPDATE_SELECTOR:
        return {&ReserveBalanceContract::precompile_update, UPDATE_OP_COST};
    default:
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_TRAITS(ReserveBalanceContract::precompile_dispatch);

Result<byte_string> ReserveBalanceContract::precompile_update(
    byte_string_view input, evmc_address const &sender,
    evmc_bytes32 const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(u256_be::from_bytes(msg_value)));
    BOOST_OUTCOME_TRY(auto new_value, abi_decode_fixed<u256_be>(input));

    if (MONAD_UNLIKELY(!input.empty())) {
        return ReserveBalanceError::InvalidInput;
    }

    if (new_value.is_zero()) {
        new_value = u256_be{DEFAULT_RESERVE_BALANCE_WEI};
    }
    auto const key = abi_encode_address(sender);
    auto const old_value = update(state_, key, new_value);
    emit_reserve_balance_changed_event(key, old_value, new_value);

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> ReserveBalanceContract::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return ReserveBalanceError::MethodNotSupported;
}

ReserveBalanceView::ReserveBalanceView(State &state)
    : state_(state)
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

uint256_t ReserveBalanceView::get(Address const &address)
{
    bytes32_t const value_be =
        state_.get_storage(RESERVE_BALANCE_CA, abi_encode_address(address));
    if (value_be == bytes32_t{}) {
        return DEFAULT_RESERVE_BALANCE_WEI;
    }
    return intx::be::load<uint256_t>(value_be.bytes);
}

MONAD_NAMESPACE_END
