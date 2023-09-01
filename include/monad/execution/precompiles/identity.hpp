#pragma once

#include <monad/execution/config.hpp>

#include <monad/core/likely.h>

#include <silkpre/precompile.h>

#include <utility>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    template <class TFork>
    struct Identity
    {
        static evmc::Result execute(evmc_message const &message) noexcept
        {
            auto const cost = silkpre_id_gas(
                message.input_data, message.input_size, TFork::rev);

            if (MONAD_UNLIKELY(std::cmp_less(message.gas, cost))) {
                return evmc::Result{evmc_result{
                    .status_code = evmc_status_code::EVMC_OUT_OF_GAS}};
            }

            return evmc::Result{
                evmc_status_code::EVMC_SUCCESS,
                /* gas_left= */ message.gas - static_cast<int64_t>(cost),
                /* gas_refund= */ 0,
                message.input_data,
                message.input_size};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END
