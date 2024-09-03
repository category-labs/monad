#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>

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

struct PrecompileResult
{
    evmc_status_code status_code;
    uint8_t *obuf;
    size_t output_size;
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

MONAD_NAMESPACE_END
