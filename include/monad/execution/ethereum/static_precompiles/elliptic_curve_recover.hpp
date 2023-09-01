#pragma once

#include <monad/execution/config.hpp>

#include <monad/core/likely.h>

#include <silkpre/precompile.h>

#include <utility>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct EllipticCurveRecover
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const cost = silkpre_ecrec_gas(
                message.input_data, message.input_size, TFork::rev);

            if (MONAD_UNLIKELY(std::cmp_less(message.gas, cost))) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const result =
                silkpre_ecrec_run(message.input_data, message.input_size);

            if (MONAD_UNLIKELY(!result.data)) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_PRECOMPILE_FAILURE}};
            }

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - static_cast<int64_t>(cost),
                .output_data = result.data,
                .output_size = result.size,
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END
