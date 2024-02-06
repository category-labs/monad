#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/system_state.hpp>
#include <monad/state3/state.hpp>

MONAD_EVM_NAMESPACE_BEGIN

SystemState::SystemState(Address const &addr, State &state)
    : addr_{addr}
    , state_{state}
{
}

bool SystemState::access_account(Address const &address)
{
    return state_.access_account(address) == EVMC_ACCESS_WARM;
}

bool SystemState::access_storage(Address const &address, bytes32_t const &key)
{
    return state_.access_storage(address, key) == EVMC_ACCESS_WARM;
}

State &SystemState::state()
{
    return state_;
}

StorageStatus SystemState::set_storage(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    MONAD_ASSERT(address == addr_);
    auto const status = state_.set_storage(address, key, value);
    return static_cast<StorageStatus>(std::to_underlying(status));
}

MONAD_EVM_NAMESPACE_END
