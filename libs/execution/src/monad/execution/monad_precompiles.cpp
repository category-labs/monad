#include <monad/execution/monad_precompiles.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <array>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using StakingPrecompilePtr =
    StakingContract::Status (StakingContract::*)(evmc_message const &);
constexpr std::array<StakingPrecompilePtr, 4> STAKING_DISPATCH{
    &StakingContract::precompile_fallback,
    &StakingContract::precompile_add_validator,
    &StakingContract::precompile_add_stake,
    &StakingContract::precompile_remove_stake};

constexpr uint32_t MONAD_STAKING_PRECOMPILES_BEGIN{0x1000};
constexpr uint32_t MONAD_STAKING_PRECOMPILES_END{
    MONAD_STAKING_PRECOMPILES_BEGIN + STAKING_DISPATCH.size() - 1};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::optional<evmc::Result>
monad_check_call_precompile(State &state, evmc_message const &msg)
{
    constexpr Address MONAD_STAKING_PRECOMPILE_END_ADDRESS{
        MONAD_STAKING_PRECOMPILES_END};

    if (msg.code_address > MONAD_STAKING_PRECOMPILE_END_ADDRESS) {
        return std::nullopt;
    }

    uint32_t const address = evmc::load32be(
        msg.code_address.bytes + sizeof(Address) - sizeof(uint32_t));

    if (address >= MONAD_STAKING_PRECOMPILES_BEGIN) {
        state.touch(STAKING_CONTRACT_ADDRESS);
        StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
        auto const offset = address - MONAD_STAKING_PRECOMPILES_BEGIN;
        auto const method = STAKING_DISPATCH[offset];
        auto const status = (contract.*method)(msg);

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
    return std::nullopt;
}

MONAD_NAMESPACE_END
