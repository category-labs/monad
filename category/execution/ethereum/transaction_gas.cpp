#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/explicit_evmc_revision.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>

#include <evmc/evmc.h>

#include <algorithm>
#include <cstdint>
#include <iterator>

MONAD_NAMESPACE_BEGIN

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
template <evmc_revision rev>
uint64_t g_data(Transaction const &tx) noexcept
{
    auto const [zeros, nonzeros] = tokens_in_calldata(tx);

    if constexpr (rev < EVMC_ISTANBUL) {
        // EIP-2028
        return zeros * 4u + nonzeros * 68u;
    }
    return zeros * 4u + nonzeros * 16u;
}

EXPLICIT_EVMC_REVISION(g_data);

template <evmc_revision rev>
uint64_t intrinsic_gas(Transaction const &tx) noexcept
{
    if constexpr (rev < EVMC_HOMESTEAD) {
        // YP, section 6.2, Eqn. 60
        return 21'000 + g_data<rev>(tx);
    }
    else if constexpr (rev < EVMC_BERLIN) {
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx);
    }
    else if constexpr (rev < EVMC_SHANGHAI) {
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx);
    }
    else {
        // EIP-3860
        return 21'000 + g_data<rev>(tx) + g_txn_create(tx) +
               g_access_and_storage(tx) + g_extra_cost_init(tx);
    }
}

EXPLICIT_EVMC_REVISION(intrinsic_gas);

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

    if (tx.type == TransactionType::eip1559) {
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

template <evmc_revision rev>
uint256_t
gas_price(Transaction const &tx, uint256_t const &base_fee_per_gas) noexcept
{
    if constexpr (rev < EVMC_LONDON) {
        return tx.max_fee_per_gas;
    }
    // EIP-1559
    return priority_fee_per_gas(tx, base_fee_per_gas) + base_fee_per_gas;
}

EXPLICIT_EVMC_REVISION(gas_price);

template <evmc_revision rev>
uint256_t calculate_txn_award(
    Transaction const &tx, uint256_t const &base_fee_per_gas,
    uint64_t const gas_used) noexcept
{
    if constexpr (rev < EVMC_LONDON) {
        return gas_used * gas_price<rev>(tx, base_fee_per_gas);
    }
    return gas_used * priority_fee_per_gas(tx, base_fee_per_gas);
}

EXPLICIT_EVMC_REVISION(calculate_txn_award);

MONAD_NAMESPACE_END
