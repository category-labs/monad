#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/state2/state.hpp>

#include <gtest/gtest.h>

using namespace monad;

using db_t = db::InMemoryTrieDB;

using traits_t = fork_traits::shanghai;
using processor_t = TransactionProcessor<traits_t>;

TEST(Validation, validate_enough_gas)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1,
        .from = a};

    auto status = static_validate_txn<traits_t>(t, 0);
    EXPECT_EQ(status, ValidationStatus::INTRINSIC_GAS_GREATER_THAN_LIMIT);
}

TEST(Validation, validate_deployed_code)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    db_t db;
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_code_hash(a, some_non_null_hash);
    s.set_nonce(a, 24);

    static Transaction const t{.gas_limit = 60'500, .from = a};

    auto status = validate_txn(s, t);
    EXPECT_EQ(status, ValidationStatus::SENDER_NOT_EOA);
}

TEST(Validation, validate_nonce)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811,
        .from = a};
    db_t db;
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);

    auto status = validate_txn(s, t);
    EXPECT_EQ(status, ValidationStatus::BAD_NONCE);
}

TEST(Validation, validate_nonce_optimistically)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811,
        .from = a};

    db_t db;
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);
    auto status = validate_txn(s, t);
    EXPECT_EQ(status, ValidationStatus::BAD_NONCE);
}

TEST(Validation, validate_enough_balance)
{
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
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 55'939'568'773'815'811);

    auto status = validate_txn(s, t);
    EXPECT_EQ(status, ValidationStatus::INSUFFICIENT_BALANCE);
}

TEST(Validation, successful_validation)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db;
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    EXPECT_EQ(static_validate_txn<traits_t>(t, 0), ValidationStatus::SUCCESS);
    EXPECT_EQ(validate_txn(s, t), ValidationStatus::SUCCESS);
}

TEST(Validation, max_fee_less_than_base)
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

    auto status = static_validate_txn<traits_t>(t, 37'000'000'000);
    EXPECT_EQ(status, ValidationStatus::MAX_FEE_LESS_THAN_BASE);
}

TEST(Validation, priority_fee_greater_than_max)
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

    auto status = static_validate_txn<traits_t>(t, 29'000'000'000);
    EXPECT_EQ(status, ValidationStatus::PRIORITY_FEE_GREATER_THAN_MAX);
}

TEST(Validation, insufficent_balance_overflow)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    db_t db;
    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, std::numeric_limits<uint256_t>::max());

    static Transaction const t{
        .max_fee_per_gas = std::numeric_limits<uint256_t>::max() - 1,
        .gas_limit = 1000,
        .value = 0,
        .to = b,
        .from = a};

    EXPECT_EQ(validate_txn(s, t), ValidationStatus::INSUFFICIENT_BALANCE);
}

// EIP-3860
TEST(Validation, init_code_exceed_limit)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    byte_string long_data;
    for (auto i = 0u; i < uint64_t{0xc002}; ++i) {
        long_data += {0xc0};
    }
    // exceed EIP-3860 limit

    static Transaction const t{
        .max_fee_per_gas = 0,
        .gas_limit = 1000,
        .value = 0,
        .from = a,
        .data = long_data};

    EXPECT_EQ(
        static_validate_txn<fork_traits::shanghai>(t, 0),
        ValidationStatus::INIT_CODE_LIMIT_EXCEEDED);
}

TEST(Validation, invalid_gas_limit)
{
    static BlockHeader const header{.gas_limit = 1000, .gas_used = 500};

    EXPECT_EQ(
        static_validate_header<fork_traits::shanghai>(header),
        ValidationStatus::INVALID_GAS_LIMIT);
}

TEST(Validation, wrong_dao_extra_data)
{
    static BlockHeader const header{
        .number = dao::dao_block_number + 5,
        .gas_limit = 10000,
        .extra_data = {0x00, 0x01, 0x02}};

    EXPECT_EQ(
        static_validate_header<fork_traits::homestead>(header),
        ValidationStatus::WRONG_DAO_EXTRA_DATA);
}

TEST(Validation, base_fee_per_gas_existence)
{
    static BlockHeader const header1{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = 1000};

    EXPECT_EQ(
        static_validate_header<fork_traits::frontier>(header1),
        ValidationStatus::FIELD_BEFORE_FORK);

    static BlockHeader const header2{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = std::nullopt};

    EXPECT_EQ(
        static_validate_header<fork_traits::london>(header2),
        ValidationStatus::MISSING_FIELD);
}

TEST(Validation, withdrawal_root_existence)
{
    static BlockHeader const header1{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = std::nullopt,
        .withdrawals_root = 0x00_bytes32};

    EXPECT_EQ(
        static_validate_header<fork_traits::frontier>(header1),
        ValidationStatus::FIELD_BEFORE_FORK);

    static BlockHeader const header2{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = 1000,
        .withdrawals_root = std::nullopt};
    EXPECT_EQ(
        static_validate_header<fork_traits::shanghai>(header2),
        ValidationStatus::MISSING_FIELD);
}

TEST(Validation, invalid_nonce)
{
    static constexpr byte_string_fixed<8> nonce{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08};

    static BlockHeader const header{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .nonce = nonce,
        .base_fee_per_gas = 1000};
    EXPECT_EQ(
        static_validate_header<fork_traits::paris>(header),
        ValidationStatus::INVALID_NONCE);
}
