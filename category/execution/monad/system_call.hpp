#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

// This address is derived from a known key. Consensus will sign all system
// transactions with this key.
inline constexpr Address SYSTEM_TRANSACTION_SENDER =
    evmc::literals::parse<evmc::address>(
        "0x6f49a8F621353f12378d0046E7d7e4b9B249DC9e");

bool is_restricted_system_call(evmc_message const &);

MONAD_NAMESPACE_END
