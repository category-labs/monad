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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

bool init_trusted_setup();

inline constexpr Address ripemd_address{3};

template <Traits traits>
bool is_precompile(Address const &, bool);

template <Traits traits>
std::optional<evmc::Result>
check_call_precompile(evmc_message const &, bool enable_p256_verify);

using precompiled_gas_cost_fn = uint64_t(byte_string_view, evmc_revision);

uint64_t ecrecover_gas_cost(byte_string_view, evmc_revision);
uint64_t sha256_gas_cost(byte_string_view, evmc_revision);
uint64_t ripemd160_gas_cost(byte_string_view, evmc_revision);
uint64_t identity_gas_cost(byte_string_view, evmc_revision);
uint64_t expmod_gas_cost(byte_string_view, evmc_revision);
uint64_t ecadd_gas_cost(byte_string_view, evmc_revision);
uint64_t ecmul_gas_cost(byte_string_view, evmc_revision);
uint64_t snarkv_gas_cost(byte_string_view, evmc_revision);
uint64_t blake2bf_gas_cost(byte_string_view, evmc_revision);
uint64_t point_evaluation_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_g1_add_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_g1_msm_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_g2_add_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_g2_msm_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_pairing_check_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_map_fp_to_g1_gas_cost(byte_string_view, evmc_revision);
uint64_t bls12_map_fp2_to_g2_gas_cost(byte_string_view, evmc_revision);

// Rollup precompiles
uint64_t p256_verify_gas_cost(byte_string_view, evmc_revision);

struct PrecompileResult
{
    evmc_status_code status_code;
    uint8_t *obuf;
    size_t output_size;

    static constexpr PrecompileResult failure() noexcept
    {
        return {
            .status_code = EVMC_PRECOMPILE_FAILURE,
            .obuf = nullptr,
            .output_size = 0,
        };
    }
};

using precompiled_execute_fn = PrecompileResult(byte_string_view);

PrecompileResult ecrecover_execute(byte_string_view);
PrecompileResult sha256_execute(byte_string_view);
PrecompileResult ripemd160_execute(byte_string_view);
PrecompileResult identity_execute(byte_string_view);
PrecompileResult expmod_execute(byte_string_view);
PrecompileResult ecadd_execute(byte_string_view);
PrecompileResult ecmul_execute(byte_string_view);
PrecompileResult snarkv_execute(byte_string_view);
PrecompileResult blake2bf_execute(byte_string_view);
PrecompileResult point_evaluation_execute(byte_string_view);
PrecompileResult bls12_g1_add_execute(byte_string_view);
PrecompileResult bls12_g1_msm_execute(byte_string_view);
PrecompileResult bls12_g2_add_execute(byte_string_view);
PrecompileResult bls12_g2_msm_execute(byte_string_view);
PrecompileResult bls12_pairing_check_execute(byte_string_view);
PrecompileResult bls12_map_fp_to_g1_execute(byte_string_view);
PrecompileResult bls12_map_fp2_to_g2_execute(byte_string_view);

// Rollup precompiles
PrecompileResult p256_verify_execute(byte_string_view);

MONAD_NAMESPACE_END
