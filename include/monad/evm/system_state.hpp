#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/evm/config.hpp>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_EVM_NAMESPACE_BEGIN

enum class StorageStatus;

// YP 9
class SystemState
{
    // TODO: also cache node cursor
    Address addr_;
    State &state_;

public:
    SystemState(Address const &, State &);

    // TODO: remove
    bool access_account(Address const &);
    bool access_storage(Address const &, bytes32_t const &key);

    State &state();

    StorageStatus
    set_storage(Address const &, bytes32_t const &key, bytes32_t const &value);
};

MONAD_EVM_NAMESPACE_END
