#include <monad/execution/monad_precompiles.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <utility>

MONAD_NAMESPACE_BEGIN

std::optional<evmc::Result>
monad_check_call_precompile(State &state, evmc_message const &msg)
{
    if (msg.code_address != STAKING_CONTRACT_ADDRESS) {
        return std::nullopt;
    }

    byte_string_view input{msg.input_data, msg.input_size};
    auto const [method, cost] = StakingContract::precompile_dispatch(input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    state.touch(STAKING_CONTRACT_ADDRESS);
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const output = (contract.*method)(input, msg.sender, msg.value);
    if (MONAD_LIKELY(output.status == StakingContract::SUCCESS)) {
        return evmc::Result{evmc_result{
            .status_code = EVMC_SUCCESS,
            .gas_left = msg.gas - static_cast<int64_t>(cost),
            .gas_refund = 0,
            .output_data = output.data.data(),
            .output_size = output.data.size(),
            .release = evmc_free_result_memory,
            .create_address = {},
            .padding = {},
        }};
    }
    std::string_view const message =
        StakingContract::error_message(output.status);
    return evmc::Result(
        EVMC_REVERT,
        0 /* gas left */,
        0 /* gas refund */,
        reinterpret_cast<uint8_t const *>(message.data()),
        message.size());
}

MONAD_NAMESPACE_END
