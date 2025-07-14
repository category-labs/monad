#pragma once

#include <category/core/config.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <monad/core/address.hpp>
#include <monad/core/signature.hpp>

#include <algorithm>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class TransactionType : char
{
    legacy = 0,
    eip2930,
    eip1559,
    LAST,
};

struct AccessEntry
{
    Address a{};
    std::vector<bytes32_t> keys{};

    friend bool operator==(AccessEntry const &, AccessEntry const &) = default;
};

static_assert(sizeof(AccessEntry) == 48);
static_assert(alignof(AccessEntry) == 8);

using AccessList = std::vector<AccessEntry>;

static_assert(sizeof(AccessList) == 24);
static_assert(alignof(AccessList) == 8);

struct Transaction
{
    SignatureAndChain sc{};
    uint64_t nonce{};
    uint256_t max_fee_per_gas{}; // gas_price
    uint64_t gas_limit{};
    uint256_t value{};
    std::optional<Address> to{};
    TransactionType type{};
    byte_string data{};
    AccessList access_list{};
    uint256_t max_priority_fee_per_gas{};

    friend bool operator==(Transaction const &, Transaction const &) = default;
};

static_assert(sizeof(Transaction) == 304);
static_assert(alignof(Transaction) == 8);

std::optional<Address> recover_sender(Transaction const &);

MONAD_NAMESPACE_END
