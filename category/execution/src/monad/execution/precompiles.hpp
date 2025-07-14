#pragma once

#include <category/core/config.hpp>
#include <monad/core/address.hpp>
#include <category/core/byte_string.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

inline constexpr Address ripemd_address{3};

template <evmc_revision rev>
bool is_precompile(Address const &) noexcept;

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &);

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

MONAD_NAMESPACE_END
