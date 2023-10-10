#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/signature.hpp>

#include <algorithm>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class TransactionType
{
    eip155, // legacy
    eip2930,
    eip1559,
};

struct Transaction
{
    struct AccessEntry
    {
        address_t a{};
        std::vector<bytes32_t> keys{};
    };

    using AccessList = std::vector<AccessEntry>;

    SignatureAndChain sc{};
    uint64_t nonce{};
    uint256_t max_fee_per_gas{}; // gas_price
    uint64_t gas_limit{};
    uint128_t amount{};
    std::optional<address_t> to{};
    std::optional<address_t> from{};
    byte_string data{};
    TransactionType type{};
    AccessList access_list{};
    uint256_t max_priority_fee_per_gas{};
};

static_assert(sizeof(Transaction::AccessEntry) == 48);
static_assert(alignof(Transaction::AccessEntry) == 8);

static_assert(sizeof(Transaction::AccessList) == 24);
static_assert(alignof(Transaction::AccessList) == 8);

static_assert(sizeof(Transaction) == 320);
static_assert(alignof(Transaction) == 8);

[[nodiscard]] std::optional<address_t> recover_sender(Transaction const &t);

MONAD_NAMESPACE_END
