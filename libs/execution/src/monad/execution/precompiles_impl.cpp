#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/execution/precompiles.hpp>

#include <evmc/evmc.h>
#include <silkpre/precompile.h>

#include <cstring>

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

PrecompileResult ecrecover_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_ecrec_run>(input);
}

PrecompileResult sha256_execute(byte_string_view const input)
{
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

MONAD_NAMESPACE_END
