#pragma once

#include "evmc/evmc.hpp"
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/signature.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct Transaction
{
    enum class Type
    {
        eip155,
        eip1559,
        eip2930,
    };

    struct AccessEntry
    {
        address_t a{};
        std::vector<bytes32_t> keys{};
    };

    using AccessList = std::vector<AccessEntry>;

    SignatureAndChain sc;
    uint64_t nonce{};
    uint64_t gas_price{};
    uint64_t gas_limit{};
    uint128_t amount{};
    std::optional<address_t> to{};
    std::optional<address_t> from{};
    byte_string data;
    Type type;
    AccessList access_list{};
    uint64_t priority_fee{};
};

static_assert(sizeof(Transaction::AccessEntry) == 48);
static_assert(alignof(Transaction::AccessEntry) == 8);

static_assert(sizeof(Transaction::AccessList) == 24);
static_assert(alignof(Transaction::AccessList) == 8);

static_assert(sizeof(Transaction) == 248);
static_assert(alignof(Transaction) == 8);

MONAD_NAMESPACE_END
