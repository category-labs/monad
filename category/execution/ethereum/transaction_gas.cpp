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
#include <category/core/bit_primitives.hpp>
#include <category/core/checked_math.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/thread_local.h>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace
{
    template <unsigned_integral UInt>
    constexpr UInt compute_priority_fee(
        TransactionType const type, UInt const &max_fee,
        UInt const &max_priority_fee, UInt const &base_fee) noexcept
    {
        MONAD_ASSERT(max_fee >= base_fee);
        UInt const fee_headroom = max_fee - base_fee;
        if (type == TransactionType::eip1559 ||
            type == TransactionType::eip4844 ||
            type == TransactionType::eip7702) {
            return std::min(max_priority_fee, fee_headroom);
        }
        // Legacy transactions pay their full gas price: the remainder is tip.
        return fee_headroom;
    }

    // Approximates `factor * e ** (n/d) using Taylor expansion
    uint256_t fake_exponential(
        uint256_t const factor, uint256_t const n, uint256_t const d)
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
constexpr auto g_txn_create(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return 32'000u;
    }
    return 0u;
}

// EIP-2930
constexpr auto g_access_and_storage(Transaction const &tx) noexcept
{
    uint64_t g = tx.access_list.size() * 2'400u;
    for (auto const &i : tx.access_list) {
        g += i.keys.size() * 1'900u;
    }
    return g;
}

// EIP-7981
// Without EIP-7976, the 64 per-byte cost specified by EIP-7981 is 40 per-byte
constexpr uint64_t g_access_list_data(Transaction const &tx) noexcept
{
    uint64_t g = tx.access_list.size() * 20u;
    for (auto const &i : tx.access_list) {
        g += i.keys.size() * 32u;
    }
    return g * 40u;
}

// EIP-7702
constexpr auto g_authorization(Transaction const &tx) noexcept
{
    constexpr uint64_t per_empty_account_cost = 25'000u;
    return per_empty_account_cost * tx.authorization_list.size();
}

constexpr uint64_t g_extra_cost_init(Transaction const &tx) noexcept
{
    if (!tx.to.has_value()) {
        return ((tx.data.length() + 31u) / 32u) * 2u;
    }
    return 0u;
}

CalldataTokens tokens_in_calldata(Transaction const &tx) noexcept
{
    // Count aligned word_count between byte-wise head and tail scans.
    // Sum nonzero bits first, converting to a byte count only once.
    auto const *cursor = tx.data.data();
    size_t remaining_bytes = tx.data.size();
    uint64_t zeros = 0;
    while (remaining_bytes != 0 &&
           (reinterpret_cast<uintptr_t>(cursor) & 7) != 0) {
        zeros += (*cursor == 0x00);
        ++cursor;
        --remaining_bytes;
    }
    size_t const word_count = remaining_bytes >> 3;
    uint64_t nonzero_bits = 0;
    for (; remaining_bytes >= 8; cursor += 8, remaining_bytes -= 8) {
        nonzero_bits += bits::nonzero_byte_bits(
            *reinterpret_cast<uint64_t const *>(cursor));
    }
    zeros += (word_count * 8u) - (nonzero_bits >> 3);
    for (; remaining_bytes != 0; ++cursor, --remaining_bytes) {
        zeros += (*cursor == 0x00);
    }
    auto const nonzeros = tx.data.size() - zeros;
    return CalldataTokens{zeros, nonzeros};
}

template <Traits traits>
uint64_t intrinsic_gas(Transaction const &tx) noexcept
{
    return intrinsic_gas_counted<traits>(tx, tokens_in_calldata(tx));
}

EXPLICIT_TRAITS(intrinsic_gas);

template <Traits traits>
uint64_t intrinsic_gas_counted(
    Transaction const &tx, CalldataTokens const calldata_tokens) noexcept
{
    static_assert(traits::evm_rev() >= EvmRevision::Berlin);

    // EIP-2930: access-list and storage-key cost (active since Berlin)
    // EIP-2028 prices the calldata bytes.
    uint64_t gas =
        21'000 + (calldata_tokens.zeros * 4u + calldata_tokens.nonzeros * 16u) +
        g_txn_create(tx) + g_access_and_storage(tx);

    // EIP-3860: per-word initcode cost
    if constexpr (traits::eip_3860_active()) {
        gas += g_extra_cost_init(tx);
    }
    // EIP-7702: authorization-list cost
    if constexpr (traits::eip_7702_active()) {
        gas += g_authorization(tx);
    }
    // EIP-7981: increase access-list cost (Amsterdam)
    if constexpr (traits::eip_7981_active()) {
        gas += g_access_list_data(tx);
    }

    return gas;
}

EXPLICIT_TRAITS(intrinsic_gas_counted);

template <Traits traits>
uint64_t floor_data_gas(Transaction const &tx) noexcept
{
    return floor_data_gas_counted<traits>(tx, tokens_in_calldata(tx));
}

EXPLICIT_TRAITS(floor_data_gas);

template <Traits traits>
uint64_t floor_data_gas_counted(
    Transaction const &tx, CalldataTokens const calldata_tokens) noexcept
{
    // EIP-7623
    uint64_t gas =
        21'000 + (calldata_tokens.zeros * 10u + calldata_tokens.nonzeros * 40u);
    if constexpr (traits::eip_7981_active()) {
        gas += g_access_list_data(tx);
    }
    return gas;
}

EXPLICIT_TRAITS(floor_data_gas_counted);

constexpr uint256_t priority_fee_per_gas(
    Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
{
    return compute_priority_fee(
        tx.type,
        tx.max_fee_per_gas,
        tx.max_priority_fee_per_gas,
        base_fee_per_gas);
}

#if defined(MONAD_ZKVM_ZISK)
namespace
{
    // Use 64-bit arithmetic only when all three fees fit.
    struct Fees64
    {
        uint64_t base_fee;
        uint64_t priority_fee;
    };

    [[gnu::always_inline]] inline std::optional<Fees64> try_compute_fees64(
        Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
    {
        auto const fits_uint64 = [](uint256_t const &x) {
            return (x[1] | x[2] | x[3]) == 0;
        };
        if (MONAD_UNLIKELY(
                !fits_uint64(tx.max_fee_per_gas) ||
                !fits_uint64(tx.max_priority_fee_per_gas) ||
                !fits_uint64(base_fee_per_gas))) {
            return std::nullopt;
        }
        uint64_t const base_fee = base_fee_per_gas[0];
        uint64_t const priority_fee = compute_priority_fee(
            tx.type,
            tx.max_fee_per_gas[0],
            tx.max_priority_fee_per_gas[0],
            base_fee);
        return Fees64{base_fee, priority_fee};
    }
}
#endif

template <Traits traits>
uint256_t
gas_price(Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
{
    if constexpr (!traits::eip_1559_header_active()) {
        return tx.max_fee_per_gas;
    }
#if defined(MONAD_ZKVM_ZISK)
    // The sum does not overflow: it is at most max_fee_per_gas.
    if (auto const fees = try_compute_fees64(tx, base_fee_per_gas);
        MONAD_LIKELY(fees.has_value())) {
        return uint256_t{fees->priority_fee + fees->base_fee};
    }
#endif
    // EIP-1559
    return priority_fee_per_gas(tx, base_fee_per_gas) + base_fee_per_gas;
}

EXPLICIT_TRAITS(gas_price);

// YP Eqn 72 - template version for each revision
template <Traits traits>
uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    constexpr auto max_refund_quotient = traits::eip_3529_active() ? 5 : 2;
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
    if constexpr (!traits::eip_1559_header_active()) {
        return gas_used * gas_price<traits>(tx, base_fee_per_gas);
    }
#if defined(MONAD_ZKVM_ZISK)
    // Two 64-bit factors produce an exact 128-bit award.
    if (auto const fees = try_compute_fees64(tx, base_fee_per_gas);
        MONAD_LIKELY(fees.has_value())) {
        unsigned __int128 const award =
            static_cast<unsigned __int128>(gas_used) * fees->priority_fee;
        return uint256_t{
            static_cast<uint64_t>(award), static_cast<uint64_t>(award >> 64)};
    }
#endif
    return gas_used * priority_fee_per_gas(tx, base_fee_per_gas);
}

EXPLICIT_TRAITS(calculate_txn_award);

uint256_t calc_blob_fee(
    Transaction const &tx, uint64_t const excess_blob_gas,
    BlobSchedule const &blob_schedule) noexcept
{
    return get_base_fee_per_blob_gas(excess_blob_gas, blob_schedule) *
           get_total_blob_gas(tx);
}

uint256_t get_base_fee_per_blob_gas(
    uint64_t const excess_blob_gas, BlobSchedule const &blob_schedule) noexcept
{
    constexpr uint256_t MIN_BASE_FEE_PER_BLOB_GAS = 1;

    // Zero excess_blob_gas gas is valid, so an empty cache needs a separate
    // flag.
    struct BlobFeeCache
    {
        uint64_t excess_blob_gas;
        uint64_t update_fraction;
        uint256_t base_fee;
        bool valid;
    };

    // Constant initialization avoids guest guard and teardown support.
    static MONAD_THREAD_LOCAL BlobFeeCache cache{};

    uint64_t const update_fraction =
        blob_schedule.blob_base_fee_update_fraction;
    if (cache.valid && cache.excess_blob_gas == excess_blob_gas &&
        cache.update_fraction == update_fraction) {
        return cache.base_fee;
    }
    uint256_t const base_fee = fake_exponential(
        MIN_BASE_FEE_PER_BLOB_GAS,
        uint256_t{excess_blob_gas},
        uint256_t{update_fraction});
    cache = BlobFeeCache{excess_blob_gas, update_fraction, base_fee, true};
    return base_fee;
}

template <Traits traits>
uint64_t calc_excess_blob_gas(
    BlockHeader const &parent_header,
    BlobSchedule const &current_blob_schedule) noexcept
{
    uint64_t const total_blob_gas = parent_header.excess_blob_gas.value_or(0) +
                                    parent_header.blob_gas_used.value_or(0);
    uint64_t const target_blob_gas =
        target_blob_gas_per_block(current_blob_schedule);

    if (total_blob_gas < target_blob_gas) {
        return 0;
    }

    if constexpr (traits::eip_7918_active()) {
        constexpr uint256_t PRICE_RATIO = GAS_PER_BLOB / BLOB_BASE_COST;

        auto const threshold = checked_mul(
            PRICE_RATIO,
            get_base_fee_per_blob_gas(
                parent_header.excess_blob_gas.value_or(0),
                current_blob_schedule));

        uint256_t const execution_base_fee =
            parent_header.base_fee_per_gas.value_or(uint256_t{});

        if (threshold && execution_base_fee > threshold.assume_value()) {
            return parent_header.excess_blob_gas.value_or(0) +
                   parent_header.blob_gas_used.value_or(0) *
                       (current_blob_schedule.max_blobs_per_block -
                        current_blob_schedule.target_blobs_per_block) /
                       current_blob_schedule.max_blobs_per_block;
        }
    }

    return total_blob_gas - target_blob_gas;
}

EXPLICIT_TRAITS(calc_excess_blob_gas);

uint64_t get_total_blob_gas(Transaction const &tx) noexcept
{
    return GAS_PER_BLOB * tx.blob_versioned_hashes.size();
}

MONAD_NAMESPACE_END
