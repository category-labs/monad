#include <monad/config.hpp>

#include <monad/db/db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state2/state.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using db_t = db::InMemoryTrieDB;
using mutex_t = std::shared_mutex;
using block_cache_t = execution::fake::BlockDb;
using state_t = state::State<mutex_t, block_cache_t>;

using traits_t = fake::traits::alpha<state_t>;
using processor_t = TransactionProcessor<state_t, traits_t>;

TEST(Execution, static_validate_no_sender)
{
    processor_t p{};
    Transaction const t{};

    EXPECT_DEATH(p.static_validate(t), "from.has_value");
}

TEST(Execution, validate_enough_gas)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .amount = 1,
        .from = a};

    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 55'939'568'773'815'811);

    traits_t::_intrinsic_gas = 53'000;

    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, TransactionStatus::INVALID_GAS_LIMIT);
}

TEST(Execution, validate_deployed_code)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_code_hash(a, some_non_null_hash);
    s.set_nonce(a, 24);
    traits_t::_intrinsic_gas = 27'500;

    static Transaction const t{.gas_limit = 27'500, .from = a};

    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, TransactionStatus::DEPLOYED_CODE);
}

TEST(Execution, validate_nonce)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .from = a};
    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);
    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, TransactionStatus::BAD_NONCE);
}

TEST(Execution, validate_nonce_optimistically)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .from = a};

    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);
    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, TransactionStatus::LATER_NONCE);
}

TEST(Execution, validate_enough_balance)
{
    processor_t p{};
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000,
    };

    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 55'939'568'773'815'811);
    traits_t::_intrinsic_gas = 21'000;

    auto status1 = p.validate(s, t, 10u);
    EXPECT_EQ(status1, TransactionStatus::INSUFFICIENT_BALANCE);
    auto status2 = p.validate(s, t, 0u); // free gas
    EXPECT_EQ(status2, TransactionStatus::SUCCESS);
}

TEST(Execution, successful_validation)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);
    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    processor_t p{};

    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, TransactionStatus::SUCCESS);
}

TEST(Execution, insufficient_balance_higher_base_fee)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);
    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000};

    processor_t p{};

    auto status = p.validate(s, t, 37'000'000'000);
    EXPECT_EQ(status, TransactionStatus::INSUFFICIENT_BALANCE);
}

TEST(Execution, successful_validation_higher_base_fee)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db;
    block_cache_t block_cache;
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);

    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 48'979'750'000'000'000,
        .to = b,
        .from = a,
        .max_priority_fee_per_gas = 100'000'000};

    processor_t p{};

    auto status = p.validate(s, t, 37'000'000'000);
    EXPECT_EQ(status, TransactionStatus::SUCCESS);
}
