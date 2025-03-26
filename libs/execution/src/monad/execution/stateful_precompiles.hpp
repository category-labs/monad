#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <cstdint>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class State;

class StatefulPrecompile
{
    State &state_;
    uint64_t const epoch_;

public:
    StatefulPrecompile(State &, uint64_t epoch);

    evmc_status_code
    create_validator(byte_string_view input, evmc_message const &);
    evmc_status_code
    stake_withdraw(byte_string_view input, evmc_message const &);
};

MONAD_NAMESPACE_END
