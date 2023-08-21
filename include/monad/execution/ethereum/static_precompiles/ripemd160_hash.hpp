#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>
#include <silkpre/rmd160.h>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct Ripemd160Hash
    {
        using gas_cost = typename TFork::ripemd160_gas_t;
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const cost = gas_cost::compute(message.input_size);
            if (message.gas < cost) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            bytes32_t output{};
            silkpre_rmd160(
                output.bytes, message.input_data, message.input_size);

            return evmc::Result{
                evmc_status_code::EVMC_SUCCESS,
                /* gas_left= */ message.gas - cost,
                /* gas_refund= */ 0,
                output.bytes,
                sizeof(bytes32_t)};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END