#pragma once

#include <monad/core/assert.h>
#include <monad/execution/config.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace static_precompiles
{
    // IdentityBaseGas uint64 = 15 // Base price for a data copy operation
    // IdentityPerWordGas uint64 = 3 // Per-work price for a data copy operation

    template <class TState, concepts::fork_traits<TState> TTraits>
    struct Identity
    {
        static constexpr auto BaseGas = 15;
        static constexpr auto PerWordGas = 3;

        // what type should we use for gas? int64_t not as descriptive? also
        // wtf is there to be aware of with respect to overflowing?
        [[nodiscard]] static int64_t required_gas(evmc_message const &message)
        {
            return static_cast<int64_t>(message.input_size + 31) / 32 *
                       PerWordGas +
                   BaseGas;
        }

        static evmc_result execute(evmc_message const &message) noexcept
        {
            auto const gas = required_gas(message);
            if (message.gas < gas) {
                return {.status_code = EVMC_OUT_OF_GAS};
            }

            std::vector<std::byte> output_data;
            output_data.reserve(message.input_size);

            std::memcpy(
                output_data.data(), message.input_data, message.input_size);
            return {
                .status_code = EVMC_SUCCESS,
                .gas_left = message.gas - gas,
                .output_data = output_data,
                .output_size = message.input_size,
                .release = [](const evmc_result *result) {
                    std::free((unsigned char *)result->output_data);
                }};
        }
    };
}

MONAD_EXECUTION_NAMESPACE_END