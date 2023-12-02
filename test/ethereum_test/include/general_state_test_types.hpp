#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/test/config.hpp>

#include <intx/intx.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_TEST_NAMESPACE_BEGIN

struct Indices
{
    uint64_t input{};
    uint64_t gas_limit{};
    uint64_t value{};
};

struct SharedTransactionData
{
    std::vector<AccessList> access_lists;
    std::vector<byte_string> inputs;
    std::vector<uint64_t> gas_limits;
    std::vector<uint256_t> values;

    // the following fields are shared among all transactions in a test file
    uint64_t nonce;
    Address sender;
    std::optional<Address> to;
    TransactionType transaction_type;
    uint256_t max_fee_per_gas;
    uint256_t max_priority_fee_per_gas;
};

struct Expectation
{
    Indices indices;
    bytes32_t state_hash;
    TransactionError error;
};

MONAD_TEST_NAMESPACE_END
