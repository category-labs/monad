#include <monad/config.hpp>

#include <monad/db/db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/state2/state.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using db_t = db::InMemoryTrieDB;
using mutex_t = std::shared_mutex;
using state_t = state::State<mutex_t>;

using traits_t = fork_traits::shanghai;
using processor_t = TransactionProcessor<state_t, traits_t>;

TEST(Execution, validate_enough_gas)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1,
        .from = a};

    auto status = p.static_validate(t, 0);
    EXPECT_EQ(status, TransactionStatus::INTRINSIC_GAS_GREATER_THAN_LIMIT);
}

TEST(Execution, validate_deployed_code)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_code_hash(a, some_non_null_hash);
    s.set_nonce(a, 24);

    static Transaction const t{.gas_limit = 60'500, .from = a};

    auto status = p.validate(s, t);
    EXPECT_EQ(status, TransactionStatus::SENDER_NOT_EOA);
}

TEST(Execution, validate_nonce)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811,
        .from = a};
    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);

    auto status = p.validate(s, t);
    EXPECT_EQ(status, TransactionStatus::BAD_NONCE);
}

TEST(Execution, validate_nonce_optimistically)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811,
        .from = a};

    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);
    auto status = p.validate(s, t);
    EXPECT_EQ(status, TransactionStatus::BAD_NONCE);
}

TEST(Execution, validate_enough_balance)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000,
    };

    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 55'939'568'773'815'811);

    auto status = p.validate(s, t);
    EXPECT_EQ(status, TransactionStatus::INSUFFICIENT_BALANCE);
}

TEST(Execution, successful_validation)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    processor_t p{};

    EXPECT_EQ(p.static_validate(t, 0), TransactionStatus::SUCCESS);
    EXPECT_EQ(p.validate(s, t), TransactionStatus::SUCCESS);
}

TEST(Execution, max_fee_less_than_base)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000};

    processor_t p{};

    auto status = p.static_validate(t, 37'000'000'000);
    EXPECT_EQ(status, TransactionStatus::MAX_FEE_LESS_THAN_BASE);
}

TEST(Execution, priority_fee_greater_than_max)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 48'979'750'000'000'000,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000'000};

    processor_t p{};

    auto status = p.static_validate(t, 29'000'000'000);
    EXPECT_EQ(status, TransactionStatus::PRIORITY_FEE_GREATER_THAN_MAX);
}

TEST(Execution, insufficent_balance_overflow)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, std::numeric_limits<uint256_t>::max());

    static Transaction const t{
        .max_fee_per_gas = std::numeric_limits<uint256_t>::max() - 1,
        .gas_limit = 1000,
        .value = 0,
        .to = b,
        .from = a};

    processor_t p{};

    auto status = p.validate(s, t);
    EXPECT_EQ(status, TransactionStatus::INSUFFICIENT_BALANCE);
}
