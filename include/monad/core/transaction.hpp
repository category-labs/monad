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

struct Transaction
{
    enum class Type
    {
        eip155,
        eip2930,
        eip1559,
    };

    struct AccessEntry
    {
        address_t a{};
        std::vector<bytes32_t> keys{};
    };

    using AccessList = std::vector<AccessEntry>;

    SignatureAndChain sc;
    uint64_t nonce{};
    uint64_t gas_price{}; // max per gas fee
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

// EIP-1559
inline uint64_t per_gas_priority_fee(
    Transaction const &t, uint64_t const base_fee_per_gas)
{
    return std::min(t.priority_fee, t.gas_price - base_fee_per_gas);
}

inline uint64_t
per_gas_cost(Transaction const &t, uint64_t const base_fee_per_gas)
{
    return per_gas_priority_fee(t, base_fee_per_gas) + base_fee_per_gas;
}

MONAD_NAMESPACE_END
