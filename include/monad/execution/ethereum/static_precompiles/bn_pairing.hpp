#pragma once

#include <monad/execution/ethereum/config.hpp>
#include <silkpre/precompile.h>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct BNPairing
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            // YP Appendix E.1 Eq 269
            auto const k = message.input_size / 192;
            // YP Appendix E.1 Eq 270
            auto const unsigned_cost = TFork::bn_pairing_base_gas +
                                       TFork::bn_pairing_per_point_gas * k;

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
                silkpre_snarkv_run(message.input_data, message.input_size);

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - signed_cost,
                .output_data = result.data,
                .output_size = result.size,
                // `silkpre_snarkv_run` allocates a buffer with malloc to
                // contain the result, so it is crucial to set the release
                // member variable
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END