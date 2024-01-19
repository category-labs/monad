#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>

using namespace monad;

using db_t = db::TrieDb;

TEST(Validation, validate_enough_gas)
{
    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1};

    auto const result = static_validate_transaction<EVMC_SHANGHAI>(t, 0);
    EXPECT_EQ(result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
}

TEST(Validation, validate_deployed_code)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_code_hash(a, some_non_null_hash);
    s.set_nonce(a, 24);

    static Transaction const t{.gas_limit = 60'500};

    auto const result = validate_transaction(s, t, a);
    EXPECT_EQ(result.error(), TransactionError::SenderNotEoa);
}

TEST(Validation, validate_nonce)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};
    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);

    auto const result = validate_transaction(s, t, a);
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
}

TEST(Validation, validate_nonce_optimistically)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};

    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 24);

    auto const result = validate_transaction(s, t, a);
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
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
        .max_priority_fee_per_gas = 100'000'000,
    };

    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, 55'939'568'773'815'811);

    auto const result = validate_transaction(s, t, a);
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

TEST(Validation, successful_validation)
{
    using intx::operator"" _u256;

    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};
    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, 56'939'568'773'815'811);
    s.set_nonce(a, 25);

    static Transaction const t{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b};

    auto const result1 = static_validate_transaction<EVMC_SHANGHAI>(t, 0);
    EXPECT_TRUE(!result1.has_error());

    auto const result2 = validate_transaction(s, t, a);
    EXPECT_TRUE(!result2.has_error());
}

TEST(Validation, max_fee_less_than_base)
{
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .max_priority_fee_per_gas = 100'000'000};

    auto const result =
        static_validate_transaction<EVMC_SHANGHAI>(t, 37'000'000'000);
    EXPECT_EQ(result.error(), TransactionError::MaxFeeLessThanBase);
}

TEST(Validation, priority_fee_greater_than_max)
{
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 48'979'750'000'000'000,
        .to = b,
        .max_priority_fee_per_gas = 100'000'000'000};

    auto const result =
        static_validate_transaction<EVMC_SHANGHAI>(t, 29'000'000'000);
    EXPECT_EQ(result.error(), TransactionError::PriorityFeeGreaterThanMax);
}

TEST(Validation, insufficent_balance_overflow)
{
    static constexpr auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    db_t db{mpt::DbOptions{.on_disk = false}};
    BlockState bs{db};
    State s{bs};
    s.add_to_balance(a, std::numeric_limits<uint256_t>::max());

    static Transaction const t{
        .max_fee_per_gas = std::numeric_limits<uint256_t>::max() - 1,
        .gas_limit = 1000,
        .value = 0,
        .to = b};

    auto const result = validate_transaction(s, t, a);
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

// EIP-3860
TEST(Validation, init_code_exceed_limit)
{
    byte_string long_data;
    for (auto i = 0u; i < uint64_t{0xc002}; ++i) {
        long_data += {0xc0};
    }
    // exceed EIP-3860 limit

    static Transaction const t{
        .max_fee_per_gas = 0, .gas_limit = 1000, .value = 0, .data = long_data};

    auto const result = static_validate_transaction<EVMC_SHANGHAI>(t, 0);
    EXPECT_EQ(result.error(), TransactionError::InitCodeLimitExceeded);
}

TEST(Validation, invalid_gas_limit)
{
    static BlockHeader const header{.gas_limit = 1000, .gas_used = 500};

    auto const result = static_validate_header<EVMC_SHANGHAI>(header);
    EXPECT_EQ(result.error(), BlockError::InvalidGasLimit);
}

TEST(Validation, wrong_dao_extra_data)
{
    static BlockHeader const header{
        .number = dao::dao_block_number + 5,
        .gas_limit = 10000,
        .extra_data = {0x00, 0x01, 0x02}};

    auto const result = static_validate_header<EVMC_HOMESTEAD>(header);
    EXPECT_EQ(result.error(), BlockError::WrongDaoExtraData);
}

TEST(Validation, base_fee_per_gas_existence)
{
    static BlockHeader const header1{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = 1000};

    auto const result1 = static_validate_header<EVMC_FRONTIER>(header1);
    EXPECT_EQ(result1.error(), BlockError::FieldBeforeFork);

    static BlockHeader const header2{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = std::nullopt};

    auto const result2 = static_validate_header<EVMC_LONDON>(header2);
    EXPECT_EQ(result2.error(), BlockError::MissingField);
}

TEST(Validation, withdrawal_root_existence)
{
    static BlockHeader const header1{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = std::nullopt,
        .withdrawals_root = 0x00_bytes32};

    auto const result1 = static_validate_header<EVMC_FRONTIER>(header1);
    EXPECT_EQ(result1.error(), BlockError::FieldBeforeFork);

    static BlockHeader const header2{
        .ommers_hash = NULL_LIST_HASH,
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = 1000,
        .withdrawals_root = std::nullopt};

    auto const result2 = static_validate_header<EVMC_SHANGHAI>(header2);
    EXPECT_EQ(result2.error(), BlockError::MissingField);
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

    auto const result = static_validate_header<EVMC_PARIS>(header);
    EXPECT_EQ(result.error(), BlockError::InvalidNonce);
}
