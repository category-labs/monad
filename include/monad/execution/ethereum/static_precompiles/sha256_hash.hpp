#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/ethereum/config.hpp>
#include <silkpre/sha256.h>

MONAD_EXECUTION_ETHEREUM_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct Sha256Hash
    {
        using gas_cost = typename TFork::sha256_gas_t;
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const cost = gas_cost::compute(message.input_size);

            if (message.gas < cost) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            bytes32_t output{};
            silkpre_sha256(
                output.bytes,
                message.input_data,
                message.input_size,
                /* use_cpu_extensions */ true);

            return evmc::Result{
                evmc_status_code::EVMC_SUCCESS,
                /* gas_left= */ message.gas - cost,
                /* gas_refund= */ 0,
                output.bytes,
                sizeof(bytes32_t)};
        }
    };
}

MONAD_EXECUTION_ETHEREUM_NAMESPACE_END