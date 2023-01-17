#pragma once

#include "evmc/evmc.hpp"
#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

namespace legacy
{
    struct Transaction
    {
        uint256_t r{}, s{};
        uint128_t amount{};
        uint64_t gasPrice{};
        uint64_t gasLimit{};
        byte_string data;
        uint64_t nonce{};
        uint16_t v{};
        std::optional<evmc::address> to{std::nullopt};
    };
}

MONAD_NAMESPACE_END
