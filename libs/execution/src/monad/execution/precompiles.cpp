#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/precompiles.hpp>

#include <silkpre/precompile.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/helpers.h>

#include <array>
#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

consteval unsigned num_precompiles(evmc_revision const rev)
{
    switch (rev) {
    case EVMC_FRONTIER:
    case EVMC_HOMESTEAD:
    case EVMC_TANGERINE_WHISTLE:
    case EVMC_SPURIOUS_DRAGON:
        return 4;
    case EVMC_BYZANTIUM:
    case EVMC_CONSTANTINOPLE:
    case EVMC_PETERSBURG:
        return 8;
    case EVMC_ISTANBUL:
    case EVMC_BERLIN:
    case EVMC_LONDON:
    case EVMC_PARIS:
    case EVMC_SHANGHAI:
        return 9;
    case EVMC_CANCUN:
        return 10;
    case EVMC_PRAGUE:
        return 17;
    default:
        MONAD_ASSERT(false);
    }
}

template <evmc_revision rev>
bool is_precompile(Address const &address) noexcept
{
    static constexpr auto max_address = Address{num_precompiles(rev)};

    if (MONAD_LIKELY(address > max_address)) {
        return false;
    }

    if (MONAD_UNLIKELY(evmc::is_zero(address))) {
        return false;
    }

    return true;
}

EXPLICIT_EVMC_REVISION(is_precompile);

struct PrecompiledContract
{
    precompiled_gas_cost_fn *gas_cost_func;
    precompiled_execute_fn *execute_func;
};

inline constexpr std::array<
    PrecompiledContract, num_precompiles(EVMC_PRAGUE) + 1>
    dispatch{{
        {nullptr, nullptr}, // precompiles start at address 0x1
        {ecrecover_gas_cost, ecrecover_execute},
        {sha256_gas_cost, sha256_execute},
        {ripemd160_gas_cost, ripemd160_execute},
        {identity_gas_cost, identity_execute},
        {expmod_gas_cost, expmod_execute},
        {ecadd_gas_cost, ecadd_execute},
        {ecmul_gas_cost, ecmul_execute},
        {snarkv_gas_cost, snarkv_execute},
        {blake2bf_gas_cost, blake2bf_execute},
        {nullptr, nullptr}, // TODO(BSC):
                            // https://github.com/category-labs/monad/pull/968
        {bls12_g1_add_gas_cost, bls12_g1_add_execute},
        {bls12_g1_msm_gas_cost, bls12_g1_msm_execute},
        {bls12_g2_add_gas_cost, bls12_g2_add_execute},
        {bls12_g2_msm_gas_cost, bls12_g2_msm_execute},
        {bls12_pairing_check_gas_cost, bls12_pairing_check_execute},
        {bls12_map_fp_to_g1_gas_cost, bls12_map_fp_to_g1_execute},
        {bls12_map_fp2_to_g2_gas_cost, bls12_map_fp2_to_g2_execute},
    }};

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &msg)
{
    auto const &address = msg.code_address;

    if (!is_precompile<rev>(address)) {
        return std::nullopt;
    }

    auto const i = address.bytes[sizeof(address.bytes) - 1];
    auto const [gas_cost_func, execute_func] = dispatch[i];

    byte_string_view const input{msg.input_data, msg.input_size};
    uint64_t const cost = gas_cost_func(input, rev);

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

EXPLICIT_EVMC_REVISION(check_call_precompile);

MONAD_NAMESPACE_END
