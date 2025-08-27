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
#include <category/execution/ethereum/explicit_evm_chain.hpp>
#include <category/execution/ethereum/precompiles.hpp>

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

template <Traits traits>
std::optional<PrecompiledContract>
resolve_precompile(Address const &address, bool const enable_p256_verify)
{
#define CASE(addr, first_rev, name)                                            \
    do {                                                                       \
        if (MONAD_UNLIKELY(Address{(addr)} == address)) {                      \
            return since<(first_rev), traits::evm_rev()>(                      \
                {name##_gas_cost, name##_execute});                            \
        }                                                                      \
    }                                                                          \
    while (false)

#define CASE_DYN(addr, cond, name)                                             \
    do {                                                                       \
        if (MONAD_UNLIKELY(Address{(addr)} == address && (cond))) {            \
            return PrecompiledContract{name##_gas_cost, name##_execute};       \
        }                                                                      \
    }                                                                          \
    while (false)

    // Ethereum precompiles
    CASE(0x01, EVMC_FRONTIER, ecrecover);
    CASE(0x02, EVMC_FRONTIER, sha256);
    CASE(0x03, EVMC_FRONTIER, ripemd160);
    CASE(0x04, EVMC_FRONTIER, identity);
    CASE(0x05, EVMC_BYZANTIUM, expmod);
    CASE(0x06, EVMC_BYZANTIUM, ecadd);
    CASE(0x07, EVMC_BYZANTIUM, ecmul);
    CASE(0x08, EVMC_BYZANTIUM, snarkv);
    CASE(0x09, EVMC_ISTANBUL, blake2bf);
    CASE(0x0A, EVMC_CANCUN, point_evaluation);
    CASE(0x0B, EVMC_PRAGUE, bls12_g1_add);
    CASE(0x0C, EVMC_PRAGUE, bls12_g1_msm);
    CASE(0x0D, EVMC_PRAGUE, bls12_g2_add);
    CASE(0x0E, EVMC_PRAGUE, bls12_g2_msm);
    CASE(0x0F, EVMC_PRAGUE, bls12_pairing_check);
    CASE(0x10, EVMC_PRAGUE, bls12_map_fp_to_g1);
    CASE(0x11, EVMC_PRAGUE, bls12_map_fp2_to_g2);

    // Rollup precompiles
    CASE_DYN(0x0100, enable_p256_verify, p256_verify);

#undef CASE
#undef CASE_DYN

    return std::nullopt;
}

EXPLICIT_EVM_CHAIN(resolve_precompile);

template <Traits traits>
bool is_precompile(Address const &address, bool const enable_p256_verify)
{
    return resolve_precompile<traits>(address, enable_p256_verify).has_value();
}

EXPLICIT_EVM_CHAIN(is_precompile);

template <Traits traits>
std::optional<evmc::Result>
check_call_precompile(evmc_message const &msg, bool const enable_p256_verify)
{
    auto const &address = msg.code_address;
    auto const maybe_precompile =
        resolve_precompile<traits>(address, enable_p256_verify);

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
    uint64_t const cost = gas_cost_func(input, traits::evm_rev());

    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const [status_code, output_buffer, output_size] = execute_func(input);
    return evmc::Result{evmc_result{
        .status_code = status_code,
        .gas_left = (status_code == EVMC_SUCCESS)
                        ? msg.gas - static_cast<int64_t>(cost)
                        : 0,
        .gas_refund = 0,
        .output_data = output_buffer,
        .output_size = output_size,
        .release = evmc_free_result_memory,
        .create_address = {},
        .padding = {},
    }};
}

EXPLICIT_EVM_CHAIN(check_call_precompile);

MONAD_NAMESPACE_END
