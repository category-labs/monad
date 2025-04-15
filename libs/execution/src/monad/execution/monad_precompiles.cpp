#include <monad/execution/monad_precompiles.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

std::optional<evmc::Result>
monad_check_call_precompile(State &state, evmc_message const &msg)
{
    if (msg.code_address != STAKING_CONTRACT_ADDRESS) {
        return std::nullopt;
    }

    state.touch(STAKING_CONTRACT_ADDRESS);
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const status = contract.precompile_dispatch(msg);
    std::string_view message = StakingContract::error_message(status);
    auto const gas_left =
        status == StakingContract::SUCCESS ? 0 /* fixme */ : 0;
    return evmc::Result(
        EVMC_REVERT,
        gas_left,
        0 /* gas refund */,
        reinterpret_cast<uint8_t const *>(message.data()),
        message.size());
}

MONAD_NAMESPACE_END
