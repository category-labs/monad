#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <silkpre/precompile.h>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct Blake2F
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const unsigned_cost = silkpre_blake2_f_gas(
                message.input_data, message.input_size, TFork::rev);

            if (unsigned_cost > std::numeric_limits<int64_t>::max()) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_PRECOMPILE_FAILURE}};
            }

            auto const signed_cost = static_cast<int64_t>(unsigned_cost);

            if (message.gas < signed_cost) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const result =
                silkpre_blake2_f_run(message.input_data, message.input_size);

            if (!result.data) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_PRECOMPILE_FAILURE}};
            }

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - signed_cost,
                .output_data = result.data,
                .output_size = result.size,
                // In the success case, `silkpre_blake2_f_run` allocates a
                // buffer with malloc to contain the result, so it is crucial to
                // set the release member variable
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END