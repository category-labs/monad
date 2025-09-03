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

#include <category/execution/monad/min_base_fee.h>
#include <category/execution/monad/monad_transaction_gas.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
uint64_t compute_gas_refund(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        // Monad specification §4.2: Storage Gas Cost and Refunds
        return refund;
    }
    else if constexpr (traits::monad_rev() >= MONAD_ONE) {
        return 0;
    }

    return g_star<traits>(tx, gas_remaining, refund);
}

EXPLICIT_MONAD_TRAITS(compute_gas_refund);

template <Traits traits>
uint256_t
refund_gas_price(Transaction const &tx, uint256_t const &base_fee_per_gas)
{
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        // Monad specification §4.2: Storage Gas Cost and Refunds
        return monad_min_base_fee_wei(traits::monad_rev());
    }

    return gas_price<traits>(tx, base_fee_per_gas);
}

EXPLICIT_MONAD_TRAITS(refund_gas_price);

MONAD_NAMESPACE_END
