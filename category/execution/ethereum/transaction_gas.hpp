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

#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct Transaction;

template <evmc_revision rev>
uint64_t g_data(Transaction const &) noexcept;

template <evmc_revision rev>
uint64_t intrinsic_gas(Transaction const &) noexcept;

uint64_t floor_data_gas(Transaction const &) noexcept;

template <evmc_revision rev>
uint256_t
gas_price(Transaction const &, uint256_t const &base_fee_per_gas) noexcept;

template <evmc_revision rev>
uint256_t calculate_txn_award(
    Transaction const &, uint256_t const &base_fee_per_gas,
    uint64_t gas_used) noexcept;

inline intx::uint512
max_gas_cost(uint64_t const gas_limit, uint256_t max_fee_per_gas) noexcept
{
    return intx::umul(uint256_t{gas_limit}, max_fee_per_gas);
}

MONAD_NAMESPACE_END
