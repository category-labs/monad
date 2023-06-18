#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <silkpre/precompile.h>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct BNAdd
    {
        using gas_cost = typename TFork::bn_add_gas_t;
        static evmc::Result execute(const evmc_message &message) noexcept
        {
            auto const cost = gas_cost::compute(message.input_size);
            if (message.gas < cost) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const result =
                silkpre_bn_add_run(message.input_data, message.input_size);

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - cost,
                .output_data = result.data,
                .output_size = result.size,
                // `silkpre_bn_add_run` allocates a buffer with malloc to
                // contain the result, so it is crucial to set the release
                // member variable
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END