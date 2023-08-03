#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/ethereum/config.hpp>
#include <silkpre/precompile.h>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct EllipticCurveRecover
    {
        using gas_cost = typename TFork::elliptic_curve_recover_gas_t;
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            constexpr auto cost = gas_cost::base::value;

            if (message.gas < cost) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const result =
                silkpre_ecrec_run(message.input_data, message.input_size);

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - cost,
                .output_data = result.data,
                .output_size = result.size,
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END