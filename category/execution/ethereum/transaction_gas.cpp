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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <algorithm>
#include <cstdint>
#include <iterator>

MONAD_NAMESPACE_BEGIN

namespace
{
    // Approximates `factor * e ** (n/d) using Taylor expansion
    uint256_t fake_exponential(uint256_t factor, uint256_t n, uint256_t d)
    {
        int i = 1;
        uint256_t output = 0;
        uint256_t acc = factor * d;
        while (acc > 0) {
            output += acc;
            acc = (acc * n) / (d * i);
            ++i;
        }
        return output / d;
    }
}

// Intrinsic gas related functions
inline constexpr auto g_txn_create(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return 32'000u;
    }
    return 0u;
}

// EIP-2930
inline constexpr auto g_access_and_storage(Transaction const &tx) noexcept
{
    uint64_t g = tx.access_list.size() * 2'400u;
    for (auto const &i : tx.access_list) {
        g += i.keys.size() * 1'900u;
    }
    return g;
}

// EIP-7702
inline constexpr auto g_authorization(Transaction const &tx) noexcept
{
    constexpr uint64_t per_empty_account_cost = 25'000u;
    return per_empty_account_cost * tx.authorization_list.size();
}

inline constexpr uint64_t g_extra_cost_init(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return ((tx.data.length() + 31u) / 32u) * 2u;
    }
    return 0u;
}

std::pair<uint64_t, uint64_t> tokens_in_calldata(Transaction const &tx) noexcept
{
    auto const zeros = static_cast<uint64_t>(std::count_if(
        std::cbegin(tx.data), std::cend(tx.data), [](unsigned char c) {
            return c == 0x00;
        }));
    auto const nonzeros = tx.data.size() - zeros;
    return {zeros, nonzeros};
}

// YP, Eqn. 60, first summation
template <Traits traits>
uint64_t g_data(Transaction const &tx) noexcept
{
    auto const [zeros, nonzeros] = tokens_in_calldata(tx);

    if constexpr (traits::evm_rev() < EVMC_ISTANBUL) {
        // EIP-2028
        return zeros * 4u + nonzeros * 68u;
    }
    return zeros * 4u + nonzeros * 16u;
}

EXPLICIT_TRAITS(g_data);

template <Traits traits>
uint64_t intrinsic_gas(Transaction const &tx) noexcept
{
    if constexpr (traits::evm_rev() < EVMC_HOMESTEAD) {
        // YP, section 6.2, Eqn. 60
        return 21'000 + g_data<traits>(tx);
    }
    else if constexpr (traits::evm_rev() < EVMC_BERLIN) {
        return 21'000 + g_data<traits>(tx) + g_txn_create(tx);
    }
    else if constexpr (traits::evm_rev() < EVMC_SHANGHAI) {
        return 21'000 + g_data<traits>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx);
    }
    else if constexpr (traits::evm_rev() < EVMC_CANCUN) {
        // EIP-3860
        return 21'000 + g_data<traits>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx) + g_extra_cost_init(tx);
    }
    else {
        // EIP-7702
        return 21'000 + g_data<traits>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx) + g_extra_cost_init(tx) +
               g_authorization(tx);
    }
}

EXPLICIT_TRAITS(intrinsic_gas);

uint64_t floor_data_gas(Transaction const &tx) noexcept
{
    auto const [zeros, nonzeros] = tokens_in_calldata(tx);
    return 21'000 + (zeros * 10u + nonzeros * 40u);
}

inline constexpr uint256_t priority_fee_per_gas(
    Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
{
    MONAD_ASSERT(tx.max_fee_per_gas >= base_fee_per_gas);
    auto const max_priority_fee_per_gas = tx.max_fee_per_gas - base_fee_per_gas;

    if (tx.type == TransactionType::eip1559 ||
        tx.type == TransactionType::eip4844 ||
        tx.type == TransactionType::eip7702) {
        return std::min(tx.max_priority_fee_per_gas, max_priority_fee_per_gas);
    }
    // EIP-1559: "Legacy Ethereum transactions will still work and
    // be included in blocks, but they will not benefit directly from
    // the new pricing system. This is due to the fact that upgrading
    // from legacy transactions to new transactions results in the
    // legacy transaction’s gas_price entirely being consumed either
    // by the base_fee_per_gas and the priority_fee_per_gas."
    return max_priority_fee_per_gas;
}

template <Traits traits>
uint256_t
gas_price(Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
{
    if constexpr (traits::evm_rev() < EVMC_LONDON) {
        return tx.max_fee_per_gas;
    }
    // EIP-1559
    return priority_fee_per_gas(tx, base_fee_per_gas) + base_fee_per_gas;
}

EXPLICIT_TRAITS(gas_price);

uint256_t gas_price(
    evmc_revision rev, Transaction const &tx,
    uint256_t const &base_fee_per_gas) noexcept
{
    SWITCH_EVM_TRAITS(gas_price, tx, base_fee_per_gas);
    MONAD_ABORT("invalid revision");
}

// YP Eqn 72 - template version for each revision
template <Traits traits>
uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient =
        traits::evm_rev() >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (tx.gas_limit - gas_remaining) / max_refund_quotient;
    return gas_remaining + std::min(refund_allowance, refund);
}

EXPLICIT_TRAITS(g_star);

template <Traits traits>
uint64_t compute_gas_refund(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    return g_star<traits>(tx, gas_remaining, refund);
}

EXPLICIT_EVM_TRAITS(compute_gas_refund);

template <Traits traits>
uint256_t calculate_txn_award(
    Transaction const &tx, uint256_t const &base_fee_per_gas,
    uint64_t const gas_used) noexcept
{
    if constexpr (traits::evm_rev() < EVMC_LONDON) {
        return gas_used * gas_price<traits>(tx, base_fee_per_gas);
    }
    return gas_used * priority_fee_per_gas(tx, base_fee_per_gas);
}

EXPLICIT_TRAITS(calculate_txn_award);

uint256_t
calc_blob_fee(Transaction const &tx, uint64_t const excess_blob_gas) noexcept
{
    return get_base_fee_per_blob_gas(excess_blob_gas) * get_total_blob_gas(tx);
}

uint256_t get_base_fee_per_blob_gas(uint64_t const excess_blob_gas) noexcept
{
    constexpr uint256_t MIN_BASE_FEE_PER_BLOB_GAS = 1;
    constexpr uint256_t BLOB_BASE_FEE_UPDATE_FRACTION = 3338477;
    return fake_exponential(
        MIN_BASE_FEE_PER_BLOB_GAS,
        uint256_t{excess_blob_gas},
        BLOB_BASE_FEE_UPDATE_FRACTION);
}

uint64_t get_total_blob_gas(Transaction const &tx) noexcept
{
    constexpr uint64_t GAS_PER_BLOB{131072};
    return GAS_PER_BLOB * tx.blob_versioned_hashes.size();
}

MONAD_NAMESPACE_END
