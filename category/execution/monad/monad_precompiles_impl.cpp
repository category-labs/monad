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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <silkpre/precompile.h>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
uint64_t ecrecover_gas_cost(byte_string_view const input)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 2 : 1;

    return pricing_factor *
           silkpre_ecrec_gas(
               input.data(), input.size(), static_cast<int>(traits::evm_rev()));
}

EXPLICIT_MONAD_TRAITS(ecrecover_gas_cost);

template <Traits traits>
uint64_t ecadd_gas_cost(byte_string_view const input)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 2 : 1;

    return pricing_factor *
           silkpre_bn_add_gas(
               input.data(), input.size(), static_cast<int>(traits::evm_rev()));
}

EXPLICIT_MONAD_TRAITS(ecadd_gas_cost);

template <Traits traits>
uint64_t ecmul_gas_cost(byte_string_view const input)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 5 : 1;

    return pricing_factor *
           silkpre_bn_mul_gas(
               input.data(), input.size(), static_cast<int>(traits::evm_rev()));
}

EXPLICIT_MONAD_TRAITS(ecmul_gas_cost);

template <Traits traits>
uint64_t snarkv_gas_cost(byte_string_view const input)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 5 : 1;

    return pricing_factor *
           silkpre_snarkv_gas(
               input.data(), input.size(), static_cast<int>(traits::evm_rev()));
}

EXPLICIT_MONAD_TRAITS(snarkv_gas_cost);

template <Traits traits>
uint64_t blake2bf_gas_cost(byte_string_view const input)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 2 : 1;

    return pricing_factor *
           silkpre_blake2_f_gas(
               input.data(), input.size(), static_cast<int>(traits::evm_rev()));
}

EXPLICIT_MONAD_TRAITS(blake2bf_gas_cost);

template <Traits traits>
uint64_t point_evaluation_gas_cost(byte_string_view)
{
    // Monad specification §4.3: Precompiles
    static constexpr auto pricing_factor =
        traits::monad_pricing_version() >= 1 ? 4 : 1;

    return pricing_factor * 50'000;
}

EXPLICIT_MONAD_TRAITS(point_evaluation_gas_cost);

MONAD_NAMESPACE_END
