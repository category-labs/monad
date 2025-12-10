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
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <silkpre/precompile.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/helpers.h>

#include <array>
#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

struct PrecompiledContract
{
    precompiled_gas_cost_fn *gas_cost_func;
    precompiled_execute_fn *execute_func;
};

// TODO(Bruce): when we enable feature flags in traits rather than raw use of
// the EVM version, refactor this code and the general precompile setup to use
// it.
template <evmc_revision First, evmc_revision Rev>
static consteval std::optional<PrecompiledContract>
since(PrecompiledContract impl)
{
    if constexpr (Rev >= First) {
        return impl;
    }

    return std::nullopt;
}

// Convert return value to std::optional if needed
template <auto f>
inline auto fmap_optional(auto a)
{
    auto r = f(a);
    if constexpr (std::is_same_v<std::optional<uint64_t>, decltype(r)>) {
        return r;
    }
    else {
        return std::optional<decltype(r)>{r};
    }
}

template <Traits traits>
std::optional<PrecompiledContract> resolve_precompile(Address const &address)
{
#define CASE(addr, gas_cost, execute)                                          \
    do {                                                                       \
        if (MONAD_UNLIKELY(Address{(addr)} == address)) {                      \
            return PrecompiledContract{fmap_optional<(gas_cost)>, (execute)};  \
        }                                                                      \
    }                                                                          \
    while (false)

    // Ethereum precompiles
    CASE(0x01, ecrecover_gas_cost<traits>, ecrecover_execute);
    CASE(0x02, sha256_gas_cost<traits>, sha256_execute);
    CASE(0x03, ripemd160_gas_cost<traits>, ripemd160_execute);
    CASE(0x04, identity_gas_cost, identity_execute);

    if constexpr (traits::evm_rev() >= EVMC_BYZANTIUM) {
        CASE(0x05, expmod_gas_cost<traits>, expmod_execute);
        CASE(0x06, ecadd_gas_cost<traits>, ecadd_execute);
        CASE(0x07, ecmul_gas_cost<traits>, ecmul_execute);
        CASE(0x08, snarkv_gas_cost<traits>, snarkv_execute);
    }

    if constexpr (traits::evm_rev() >= EVMC_ISTANBUL) {
        CASE(0x09, blake2bf_gas_cost<traits>, blake2bf_execute);
    }

    if constexpr (traits::evm_rev() >= EVMC_CANCUN) {
        CASE(0x0A, point_evaluation_gas_cost<traits>, point_evaluation_execute);
    }

    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        CASE(0x0B, bls12_g1_add_gas_cost, bls12_g1_add_execute);
        CASE(0x0C, bls12_g1_msm_gas_cost, bls12_g1_msm_execute);
        CASE(0x0D, bls12_g2_add_gas_cost, bls12_g2_add_execute);
        CASE(0x0E, bls12_g2_msm_gas_cost, bls12_g2_msm_execute);
        CASE(0x0F, bls12_pairing_check_gas_cost, bls12_pairing_check_execute);
        CASE(0x10, bls12_map_fp_to_g1_gas_cost, bls12_map_fp_to_g1_execute);
        CASE(0x11, bls12_map_fp2_to_g2_gas_cost, bls12_map_fp2_to_g2_execute);
    }

    // Rollup precompiles
    if constexpr (traits::eip_7951_active()) {
        CASE(0x0100, p256_verify_gas_cost, p256_verify_execute);
    }

#undef CASE

    return std::nullopt;
}

EXPLICIT_TRAITS(resolve_precompile);

template <Traits traits>
bool is_eth_precompile(Address const &address)
{
    return resolve_precompile<traits>(address).has_value();
}

EXPLICIT_TRAITS(is_eth_precompile);

template <Traits traits>
bool is_precompile(Address const &address)
{
    return is_eth_precompile<traits>(address);
}

EXPLICIT_EVM_TRAITS(is_precompile);

template <Traits traits>
std::optional<evmc::Result> check_call_eth_precompile(evmc_message const &msg)
{
    auto const &address = msg.code_address;
    auto const maybe_precompile = resolve_precompile<traits>(address);

    if (!maybe_precompile) {
        return std::nullopt;
    }

    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        // EIP-7702 specifies that precompiles don't actually get called when
        // they're the target of a delegation.
        auto const delegated = (msg.flags & EVMC_DELEGATED) != 0;
        if (delegated) {
            return evmc::Result{evmc_status_code::EVMC_SUCCESS, msg.gas};
        }
    }

    auto const [gas_cost_func, execute_func] = *maybe_precompile;

    byte_string_view const input{msg.input_data, msg.input_size};
    std::optional<uint64_t> const cost = gas_cost_func(input);

    // If cost is std::nullopt, the gas function got an invalid input. This is
    // currently only possible for EXPMOD with EIP-7823.
    if (!cost.has_value()) {
        return evmc::Result{evmc_status_code::EVMC_FAILURE};
    }

    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost.value()))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const [status_code, output_buffer, output_size] = execute_func(input);
    return evmc::Result{evmc_result{
        .status_code = status_code,
        .gas_left = (status_code == EVMC_SUCCESS)
                        ? msg.gas - static_cast<int64_t>(cost.value())
                        : 0,
        .gas_refund = 0,
        .output_data = output_buffer,
        .output_size = output_size,
        .release = evmc_free_result_memory,
        .create_address = {},
        .padding = {},
    }};
}

EXPLICIT_TRAITS(check_call_eth_precompile);

template <Traits traits>
std::optional<evmc::Result>
check_call_precompile(State &, CallTracerBase &, evmc_message const &msg)
{
    return check_call_eth_precompile<traits>(msg);
}

EXPLICIT_EVM_TRAITS(check_call_precompile);

MONAD_NAMESPACE_END
