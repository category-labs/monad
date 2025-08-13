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
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <blst.h>
#include <evmc/evmc.h>
#include <silkpre/precompile.h>

#include <cstring>
#include <intx/intx.hpp>

namespace
{
    constexpr size_t num_words(size_t const length)
    {
        constexpr size_t WORD_SIZE = 32;
        return (length + WORD_SIZE - 1) / WORD_SIZE;
    }
}

MONAD_NAMESPACE_BEGIN

template <SilkpreRunFunction Func>
static inline PrecompileResult silkpre_execute(byte_string_view const input)
{
    auto const [output, output_size] = Func(input.data(), input.size());
    if (output == nullptr) {
        MONAD_DEBUG_ASSERT(output_size == 0);
        return {EVMC_PRECOMPILE_FAILURE, nullptr, 0};
    }
    return {EVMC_SUCCESS, output, output_size};
}

uint64_t
ecrecover_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_ecrec_gas(input.data(), input.size(), static_cast<int>(rev));
}

uint64_t sha256_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_sha256_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t
ripemd160_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_rip160_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t identity_gas_cost(byte_string_view const input, evmc_revision)
{
    // YP eqn 232
    return 15 + 3 * num_words(input.size());
}

uint64_t ecadd_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_bn_add_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t ecmul_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_bn_mul_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t snarkv_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_snarkv_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t
blake2bf_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_blake2_f_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t expmod_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_expmod_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t point_evaluation_gas_cost(byte_string_view, evmc_revision)
{
    // TODO: https://github.com/category-labs/monad/pull/968
    return 50'000;
}

uint64_t bls12_g1_add_gas_cost(byte_string_view, evmc_revision)
{
    return 375;
}

uint64_t bls12_g1_msm_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size = bls12::G1::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 12'000 * bls12::msm_discount<bls12::G1>(k)) / 1000;
}

uint64_t bls12_g2_add_gas_cost(byte_string_view, evmc_revision)
{
    return 600;
}

uint64_t bls12_g2_msm_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size = bls12::G2::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 22'500 * bls12::msm_discount<bls12::G2>(k)) / 1000;
}

uint64_t
bls12_pairing_check_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size =
        bls12::G1::encoded_size + bls12::G2::encoded_size;

    auto const k = input.size() / pair_size;
    return 32'600 * k + 37'700;
}

uint64_t bls12_map_fp_to_g1_gas_cost(byte_string_view, evmc_revision)
{
    return 5500;
}

uint64_t bls12_map_fp2_to_g2_gas_cost(byte_string_view, evmc_revision)
{
    return 23800;
}

PrecompileResult ecrecover_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_ecrec_run>(input);
}

PrecompileResult sha256_execute(byte_string_view const input)
{
    if (MONAD_UNLIKELY(input.data() == nullptr)) {
        // Passing a null pointer to the Silkpre sha256 implementation invokes
        // undefined behaviour. We sidestep the UB here by passing a pointer to
        // the empty string instead.
        byte_string_view const nonnull{
            reinterpret_cast<unsigned char const *>(""), 0UL};
        return silkpre_execute<silkpre_sha256_run>(nonnull);
    }
    return silkpre_execute<silkpre_sha256_run>(input);
}

PrecompileResult ripemd160_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_rip160_run>(input);
}

PrecompileResult ecadd_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_bn_add_run>(input);
}

PrecompileResult ecmul_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_bn_mul_run>(input);
}

PrecompileResult identity_execute(byte_string_view const input)
{
    if (input.empty()) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto *const output = static_cast<uint8_t *>(malloc(input.size()));
    MONAD_ASSERT(output != nullptr);
    memcpy(output, input.data(), input.size());
    return {EVMC_SUCCESS, output, input.size()};
}

PrecompileResult expmod_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_expmod_run>(input);
}

PrecompileResult snarkv_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_snarkv_run>(input);
}

PrecompileResult blake2bf_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_blake2_f_run>(input);
}

PrecompileResult point_evaluation_execute(byte_string_view)
{
    // TODO: https://github.com/category-labs/monad/pull/968
    return PrecompileResult::failure();
}

PrecompileResult bls12_g1_add_execute(byte_string_view const input)
{
    return bls12::add<bls12::G1>(input);
}

PrecompileResult bls12_g1_msm_execute(byte_string_view const input)
{
    return bls12::msm<bls12::G1>(input);
}

PrecompileResult bls12_g2_add_execute(byte_string_view const input)
{
    return bls12::add<bls12::G2>(input);
}

PrecompileResult bls12_g2_msm_execute(byte_string_view const input)
{
    return bls12::msm<bls12::G2>(input);
}

PrecompileResult bls12_pairing_check_execute(byte_string_view const input)
{
    return bls12::pairing_check(input);
}

PrecompileResult bls12_map_fp_to_g1_execute(byte_string_view const input)
{
    return bls12::map_fp_to_g<bls12::G1>(input);
}

PrecompileResult bls12_map_fp2_to_g2_execute(byte_string_view const input)
{
    return bls12::map_fp_to_g<bls12::G2>(input);
}

MONAD_NAMESPACE_END
