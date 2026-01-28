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
// Gas Costs
//

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
    default:
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS(ReserveBalanceContract::precompile_dispatch);

Result<byte_string> ReserveBalanceContract::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return ReserveBalanceError::MethodNotSupported;
}

MONAD_NAMESPACE_END
