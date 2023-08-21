#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>
#include <silkpre/precompile.h>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct ModularExponentiation
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            // TODO: In the future, we can template parameterize the call to
            // `silkpre_expmod_gas` over the revision instead of passing it in
            // as an argument, but that would involve physically forking the
            // implementation.
            auto const unsigned_required_gas = silkpre_expmod_gas(
                message.input_data, message.input_size, TFork::rev);

            // `silkpre_expmod_gas` uses UINT64_MAX as a sentinel for out of gas
            if (unsigned_required_gas > std::numeric_limits<int64_t>::max()) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const signed_required_gas =
                static_cast<int64_t>(unsigned_required_gas);

            if (message.gas < signed_required_gas) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            auto const result =
                silkpre_expmod_run(message.input_data, message.input_size);

            return evmc::Result{evmc_result{
                .status_code = evmc_status_code::EVMC_SUCCESS,
                .gas_left = message.gas - signed_required_gas,
                .output_data = result.data,
                .output_size = result.size,
                // `silkpre_expmod_run` allocates a buffer with malloc to
                // contain the result, so it is crucial to set the release
                // member variable
                .release = evmc_free_result_memory}};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END