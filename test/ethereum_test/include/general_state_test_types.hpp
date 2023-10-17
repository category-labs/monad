#pragma once

#include <monad/core/transaction.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/test/config.hpp>

#include <intx/intx.hpp>

#include <optional>

MONAD_TEST_NAMESPACE_BEGIN
struct Indices
{
    uint64_t input{};
    uint64_t gas_limit{};
    uint64_t value{};
};

struct SharedTransactionData
{
    std::vector<Transaction::AccessList> access_lists;
    std::vector<byte_string> inputs;
    std::vector<uint64_t> gas_limits;
    std::vector<uint256_t> values;

    // the following fields are shared among all transactions in a test file
    uint64_t nonce;
    address_t sender;
    std::optional<address_t> to;
    TransactionType transaction_type;
    uint256_t max_fee_per_gas;
    uint256_t max_priority_fee_per_gas;
};

struct Expectation
{
    Indices indices;
    bytes32_t state_hash;
    execution::ValidationStatus exception;
};

MONAD_TEST_NAMESPACE_END
