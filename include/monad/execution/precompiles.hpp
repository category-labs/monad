#pragma once

#include <monad/core/address.hpp>
#include <monad/core/likely.h>
#include <monad/execution/config.hpp>

#include <silkpre/precompile.h>

#include <evmc/evmc.hpp>

#include <cstdint>
#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TTraits>
[[nodiscard]] constexpr bool is_precompile(address_t const &address) noexcept
{
    static_assert(TTraits::n_precompiles < UINT8_MAX);

    static constexpr auto max_address = address_t{TTraits::n_precompiles};

    if (MONAD_LIKELY(address > max_address)) {
        return false;
    }

    if (MONAD_UNLIKELY(evmc::is_zero(address))) {
        return false;
    }

    return true;
}

template <class TTraits>
std::optional<evmc::Result> check_call_precompile(evmc_message const &msg)
{
    auto const &address = msg.code_address;

    if (!is_precompile<TTraits>(address)) {
        return std::nullopt;
    }

    auto const i = address.bytes[sizeof(address.bytes) - 1];

    auto const gas_func = kSilkpreContracts[i - 1].gas;

    auto const cost = gas_func(msg.input_data, msg.input_size, TTraits::rev);

    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const run_func = kSilkpreContracts[i - 1].run;

    auto const output = run_func(msg.input_data, msg.input_size);

    if (MONAD_UNLIKELY(!output.data)) {
        return evmc::Result{evmc_status_code::EVMC_PRECOMPILE_FAILURE};
    }

    return evmc::Result{evmc_result{
        .status_code = evmc_status_code::EVMC_SUCCESS,
        .gas_left = msg.gas - static_cast<int64_t>(cost),
        .gas_refund = 0,
        .output_data = output.data,
        .output_size = output.size,
        .release = evmc_free_result_memory}};
}

MONAD_EXECUTION_NAMESPACE_END
