#pragma once

#include <monad/core/transaction.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>
#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

struct SharedTransactionData
{
    struct Indices
    {
        uint64_t input{};
        uint64_t gas_limit{};
        uint64_t value{};
    };

    std::vector<monad::Transaction::AccessList> access_lists;
    std::vector<monad::byte_string> inputs;
    std::vector<uint64_t> gas_limits;
    std::vector<intx::uint128> values;

    // the following fields are shared among all transactions in a test file
    uint64_t nonce;
    monad::address_t sender;
    monad::address_t to;
    monad::Transaction::Type transaction_type;
    uint64_t gas_price;
    uint64_t priority_fee;
};

struct Case
{
    struct Expectation
    {
        SharedTransactionData::Indices indices;
        monad::bytes32_t state_hash;
    };

    std::size_t fork_index;
    std::string fork_name;
    std::vector<Expectation> expectations;
};

struct StateTransitionTest
{
    SharedTransactionData shared_transaction_data;
    std::vector<Case> cases;
};

MONAD_TEST_NAMESPACE_END
