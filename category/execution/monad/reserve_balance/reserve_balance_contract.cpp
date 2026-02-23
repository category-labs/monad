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
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_error.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

////////////////////////
// Function Selectors //
////////////////////////

struct PrecompileSelector
{
    static constexpr uint32_t DIPPED_INTO_RESERVE =
        abi_encode_selector("dippedIntoReserve()");
};

static_assert(PrecompileSelector::DIPPED_INTO_RESERVE == 0x3a61584e);

//
// Gas Costs
//

constexpr uint64_t DIPPED_INTO_RESERVE_OP_COST = 100; // warm sload coast

constexpr uint64_t FALLBACK_COST = 40'000;

MONAD_ANONYMOUS_NAMESPACE_END

//
// Contract implementation
//

MONAD_NAMESPACE_BEGIN

ReserveBalanceContract::ReserveBalanceContract(
    State &state, CallTracerBase &tracer)
    : state_{state}
    , call_tracer_{tracer}
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

Result<void> function_not_payable(evmc_uint256be const &value)
{
    bool const all_zero = std::all_of(
        value.bytes,
        value.bytes + sizeof(evmc_uint256be),
        [](uint8_t const byte) { return byte == 0; });

    if (MONAD_UNLIKELY(!all_zero)) {
        return ReserveBalanceError::ValueNonZero;
    }
    return outcome::success();
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
    case PrecompileSelector::DIPPED_INTO_RESERVE:
        return {
            &ReserveBalanceContract::precompile_dipped_into_reserve<traits>,
            DIPPED_INTO_RESERVE_OP_COST};
    default:
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS(ReserveBalanceContract::precompile_dispatch);

template <Traits traits>
Result<byte_string> ReserveBalanceContract::precompile_dipped_into_reserve(
    byte_string_view, evmc_address const &, evmc_uint256be const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    return byte_string{
        abi_encode_bool(revert_transaction_cached<traits>(state_))};
}

EXPLICIT_MONAD_TRAITS_MEMBER(
    ReserveBalanceContract::precompile_dipped_into_reserve);

Result<byte_string> ReserveBalanceContract::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return ReserveBalanceError::MethodNotSupported;
}

MONAD_NAMESPACE_END
