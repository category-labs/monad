// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/precompiles_bls12.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <intx/intx.hpp>

#include <algorithm>
#include <cstring>
#include <limits>

namespace
{
    constexpr size_t num_words(size_t const length)
    {
        constexpr size_t WORD_SIZE = 32;
        return (length + WORD_SIZE - 1) / WORD_SIZE;
    }
}

MONAD_NAMESPACE_BEGIN

template <Traits traits>
uint64_t ecrecover_gas_cost(byte_string_view const)
{
    // YP eqn 211
    return 3'000;
}

EXPLICIT_EVM_TRAITS(ecrecover_gas_cost);

uint64_t sha256_gas_cost(byte_string_view const input)
{
    // YP eqn 223
    return 60 + 12 * num_words(input.size());
}

uint64_t ripemd160_gas_cost(byte_string_view const input)
{
    // YP eqn 226
    return 600 + 120 * num_words(input.size());
}

uint64_t identity_gas_cost(byte_string_view const input)
{
    // YP eqn 232
    return 15 + 3 * num_words(input.size());
}

template <Traits traits>
uint64_t ecadd_gas_cost(byte_string_view const)
{
    if constexpr (traits::evm_rev() >= EVMC_ISTANBUL) {
        return 150; // EIP-1108
    }
    else {
        return 500; // EIP-196
    }
}

EXPLICIT_EVM_TRAITS(ecadd_gas_cost);

template <Traits traits>
uint64_t ecmul_gas_cost(byte_string_view const)
{
    if constexpr (traits::evm_rev() >= EVMC_ISTANBUL) {
        return 6'000; // EIP-1108
    }
    else {
        return 40'000; // EIP-196
    }
}

EXPLICIT_EVM_TRAITS(ecmul_gas_cost);

template <Traits traits>
uint64_t snarkv_gas_cost(byte_string_view const input)
{
    return snarkv_gas_cost_ethereum<traits::evm_rev()>(input);
}

EXPLICIT_EVM_TRAITS(snarkv_gas_cost);

template <Traits traits>
std::optional<uint64_t> blake2bf_gas_cost(byte_string_view const input)
{
    return blake2bf_gas_cost_ethereum(input);
}

EXPLICIT_EVM_TRAITS(blake2bf_gas_cost);

template <Traits traits>
static uint256_t mult_complexity(uint256_t const &max_len) noexcept
{
    if constexpr (traits::eip_7883_active()) {
        uint256_t const words{(max_len + 7) >> 3}; // ceil(max_len/8)
        if (max_len > 32) {
            return 2 * words * words;
        }
        else {
            return 16;
        }
    }
    else if constexpr (traits::eip_2565_active()) {
        uint256_t const words{(max_len + 7) >> 3}; // ceil(max_len/8)
        return words * words;
    }
    else {
        uint256_t const max_len_squared{max_len * max_len};
        if (max_len <= 64) {
            return max_len_squared;
        }
        else if (max_len <= 1024) {
            return (max_len_squared >> 2) + 96 * max_len - 3072;
        }
        else {
            return (max_len_squared >> 4) + 480 * max_len - 199680;
        }
    }
}

template <Traits traits>
static uint256_t expmod_gas_denominator() noexcept
{
    if constexpr (traits::eip_7883_active()) {
        return 1;
    }
    else if constexpr (traits::eip_2565_active()) {
        return 3;
    }
    else {
        return 20; // Pre EIP-2565 (EIP-198)
    }
}

template <Traits traits>
uint256_t expmod_iteration_count(uint256_t exp_len256, size_t bit_len) noexcept
{
    uint256_t adjusted_exponent_len{0};
    if (exp_len256 > 32) {
        constexpr uint256_t exp_mult{traits::eip_7883_active() ? 16u : 8u};
        adjusted_exponent_len = exp_mult * (exp_len256 - 32);
    }
    if (bit_len > 1) {
        adjusted_exponent_len =
            adjusted_exponent_len + static_cast<uint256_t>(bit_len - 1);
    }

    return std::max(adjusted_exponent_len, uint256_t{1});
}

template <Traits traits>
constexpr uint64_t expmod_min_gas()
{
    if constexpr (traits::eip_7883_active()) {
        return 500;
    }
    else if constexpr (traits::eip_2565_active()) {
        return 200;
    }
    else {
        return 0; // Pre EIP-2565 (EIP-198)
    }
}

// TODO(LH): Replace calls to this function with uint256_t::load_be_unsafe when
// migrating off intx.
static uint256_t
uint256_load_partial_be(byte_string_view const input, size_t const len)
{
    if (MONAD_UNLIKELY(input.empty())) {
        return 0;
    }

    uint256_t result{};
    MONAD_VM_ASSERT(32 >= len);
    std::memcpy(
        intx::as_bytes(result) + (32 - len),
        input.data(),
        std::min(len, input.size()));
    return intx::to_big_endian(result);
}

template <Traits traits>
std::optional<uint64_t> expmod_gas_cost(byte_string_view const input)
{
    static constexpr auto min_gas{expmod_min_gas<traits>()};

    auto const base_len256 = uint256_load_partial_be(input, 32);
    auto const exp_len256 = input.length() >= 32
                                ? uint256_load_partial_be(input.substr(32), 32)
                                : uint256_t{0};
    auto const mod_len256 = input.length() >= 64
                                ? uint256_load_partial_be(input.substr(64), 32)
                                : uint256_t{0};

    // Before EIP-7883, we could shortcut when the base and modulus lengths are
    // both zero. The EIP changes this to assume that both are at least 32 bytes
    // (and thus, an input of zero for their lengths does not in fact imply the
    // minimum gas cost).
    if constexpr (!traits::eip_7883_active()) {
        if (base_len256 == 0 && mod_len256 == 0) {
            return min_gas;
        }
    }

    if constexpr (traits::eip_7823_active()) {
        // EIP-7823: each of the length inputs (base, exponent and modulus) MUST
        // be less than or equal to 8192 bits (1024 bytes).
        if (base_len256 > 1024 || exp_len256 > 1024 || mod_len256 > 1024) {
            return std::nullopt; // invalid input
        }
    }
    else if (
        count_significant_bytes(base_len256) > 8 ||
        count_significant_bytes(exp_len256) > 8 ||
        count_significant_bytes(mod_len256) > 8) {
        return std::numeric_limits<uint64_t>::max();
    }

    auto const base_len64{static_cast<uint64_t>(base_len256)};
    auto const exp_len64{static_cast<uint64_t>(exp_len256)};

    uint256_t exp_head{0}; // first 32 bytes of the exponent
    auto const exp_index = 96 + base_len64;
    if (input.length() > exp_index) { // input contains bytes of exponents
        exp_head = uint256_load_partial_be(
            input.substr(exp_index), std::min(32ul, exp_len64));
    }
    size_t const bit_len{256 - clz(exp_head)};

    uint256_t const iteration_count{
        expmod_iteration_count<traits>(exp_len256, bit_len)};

    uint256_t const max_length{std::max(mod_len256, base_len256)};
    uint256_t const gas = mult_complexity<traits>(max_length) *
                          iteration_count / expmod_gas_denominator<traits>();

    if (intx::count_significant_words(gas) > 1) {
        return std::numeric_limits<uint64_t>::max();
    }
    else {
        return std::max(min_gas, static_cast<uint64_t>(gas));
    }
}

EXPLICIT_TRAITS(expmod_gas_cost);

template <Traits>
uint64_t point_evaluation_gas_cost(byte_string_view)
{
    return 50'000;
}

EXPLICIT_EVM_TRAITS(point_evaluation_gas_cost);

uint64_t bls12_g1_add_gas_cost(byte_string_view)
{
    return 375;
}

uint64_t bls12_g1_msm_gas_cost(byte_string_view const input)
{
    static constexpr auto pair_size = bls12::G1::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 12'000 * bls12::msm_discount<bls12::G1>(k)) / 1000;
}

uint64_t bls12_g2_add_gas_cost(byte_string_view)
{
    return 600;
}

uint64_t bls12_g2_msm_gas_cost(byte_string_view const input)
{
    static constexpr auto pair_size = bls12::G2::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 22'500 * bls12::msm_discount<bls12::G2>(k)) / 1000;
}

uint64_t bls12_pairing_check_gas_cost(byte_string_view const input)
{
    static constexpr auto pair_size =
        bls12::G1::encoded_size + bls12::G2::encoded_size;

    auto const k = input.size() / pair_size;
    return 32'600 * k + 37'700;
}

uint64_t bls12_map_fp_to_g1_gas_cost(byte_string_view)
{
    return 5500;
}

uint64_t bls12_map_fp2_to_g2_gas_cost(byte_string_view)
{
    return 23800;
}

// Rollup precompiles
uint64_t p256_verify_gas_cost(byte_string_view)
{
    return 6900;
}

MONAD_NAMESPACE_END
