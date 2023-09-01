#pragma once

#include <monad/execution/config.hpp>

#include <monad/core/likely.h>

#include <silkpre/precompile.h>
#include <silkpre/sha256.h>

#include <utility>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct Sha256Hash
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const cost = silkpre_sha256_gas(
                message.input_data, message.input_size, TFork::rev);

            if (MONAD_UNLIKELY(std::cmp_less(message.gas, cost))) {
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
                /* gas_left= */ message.gas - static_cast<int64_t>(cost),
                /* gas_refund= */ 0,
                output.bytes,
                sizeof(bytes32_t)};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END
