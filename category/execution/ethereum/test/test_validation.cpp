// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/dao.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>

using namespace monad;

TEST(Validation, validate_enough_gas)
{
    static Transaction const t{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1};

    auto const result = static_validate_transaction<EvmTraits<EVMC_SHANGHAI>>(
        t, 0, std::nullopt, 1);
    EXPECT_EQ(result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
}

TEST(Validation, validate_floor_gas)
{
    Transaction const t{
        .gas_limit = 300'000,
        .data = evmc::bytes(10000, 0x01),
    };

    auto const cancun_result =
        static_validate_transaction<EvmTraits<EVMC_CANCUN>>(
            t, 0, std::nullopt, 1);
    EXPECT_NE(
        cancun_result.error(), TransactionError::IntrinsicGasGreaterThanLimit);

    auto const prague_result =
        static_validate_transaction<EvmTraits<EVMC_PRAGUE>>(
            t, 0, std::nullopt, 1);
    EXPECT_EQ(
        prague_result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
}

TEST(Validation, validate_deployed_code)
{
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};

    Transaction const tx{.gas_limit = 60'500};
    Account const sender_account{
        .balance = 56'939'568'773'815'811,
        .code_hash = some_non_null_hash,
        .nonce = 24};

    auto const result =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
    EXPECT_EQ(result.error(), TransactionError::SenderNotEoa);
}

// EIP-7702
TEST(Validation, validate_deployed_code_delegated)
{
    static constexpr auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};

    Transaction const tx{.gas_limit = 60'500};
    Account const sender_account{
        .balance = 56'939'568'773'815'811, .code_hash = some_non_null_hash};

    auto const result = validate_transaction<EvmTraits<EVMC_PRAGUE>>(
        tx,
        sender_account,
        std::vector<uint8_t>{
            0xEF, 0x01, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55,
            0x11, 0x22, 0x33, 0x44, 0x55, 0x11, 0x22, 0x33,
            0x44, 0x55, 0x11, 0x22, 0x33, 0x44, 0x55,
        });
    EXPECT_FALSE(result.has_error());
}

TEST(Validation, validate_nonce)
{
    Transaction const tx{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};
    Account const sender_account{
        .balance = 56'939'568'773'815'811, .nonce = 24};

    auto const result =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
}

TEST(Validation, validate_nonce_optimistically)
{
    Transaction const tx{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};
    Account const sender_account{
        .balance = 56'939'568'773'815'811, .nonce = 24};

    auto const result =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
}

TEST(Validation, validate_enough_balance)
{
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = b,
        .max_priority_fee_per_gas = 100'000'000,
    };
    Account const sender_account{.balance = 55'939'568'773'815'811};

    auto const result =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

TEST(Validation, successful_validation)
{
    using intx::operator""_u256;

    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
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
    Account const sender_account{
        .balance = 56'939'568'773'815'811, .nonce = 25};

    auto const result1 = static_validate_transaction<EvmTraits<EVMC_SHANGHAI>>(
        tx, 0, std::nullopt, 1);
    EXPECT_TRUE(!result1.has_error());

    auto const result2 =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
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

    auto const result = static_validate_transaction<EvmTraits<EVMC_SHANGHAI>>(
        t, 37'000'000'000, std::nullopt, 1);
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

    auto const result = static_validate_transaction<EvmTraits<EVMC_SHANGHAI>>(
        t, 29'000'000'000, std::nullopt, 1);
    EXPECT_EQ(result.error(), TransactionError::PriorityFeeGreaterThanMax);
}

TEST(Validation, insufficent_balance_overflow)
{
    static constexpr auto b{0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
        .max_fee_per_gas = std::numeric_limits<uint256_t>::max() - 1,
        .gas_limit = 1000,
        .value = 0,
        .to = b};
    Account const sender_account{
        .balance = std::numeric_limits<uint256_t>::max()};

    auto const result =
        validate_transaction<EvmTraits<EVMC_CANCUN>>(tx, sender_account, {});
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

    auto const result = static_validate_transaction<EvmTraits<EVMC_SHANGHAI>>(
        t, 0, std::nullopt, 1);
    EXPECT_EQ(result.error(), TransactionError::InitCodeLimitExceeded);
}

TEST(Validation, invalid_gas_limit)
{
    static BlockHeader const header{.gas_limit = 1000, .gas_used = 500};

    auto const result =
        static_validate_header<EvmTraits<EVMC_SHANGHAI>>(header);
    EXPECT_EQ(result.error(), BlockError::InvalidGasLimit);
}

TEST(Validation, wrong_dao_extra_data)
{
    static BlockHeader const header{
        .number = dao::dao_block_number + 5,
        .gas_limit = 10000,
        .extra_data = {0x00, 0x01, 0x02}};

    auto const result = EthereumMainnet{}.static_validate_header(header);
    EXPECT_EQ(result.error(), BlockError::WrongDaoExtraData);
}

TEST(Validation, base_fee_per_gas_existence)
{
    static BlockHeader const header1{
        .gas_limit = 10000, .gas_used = 5000, .base_fee_per_gas = 1000};

    auto const result1 =
        static_validate_header<EvmTraits<EVMC_FRONTIER>>(header1);
    EXPECT_EQ(result1.error(), BlockError::FieldBeforeFork);

    static BlockHeader const header2{
        .gas_limit = 10000, .gas_used = 5000, .base_fee_per_gas = std::nullopt};

    auto const result2 =
        static_validate_header<EvmTraits<EVMC_LONDON>>(header2);
    EXPECT_EQ(result2.error(), BlockError::MissingField);
}

TEST(Validation, withdrawal_root_existence)
{
    EthereumMainnet chain;

    static BlockHeader const header1{
        .ommers_hash = NULL_LIST_HASH,
        .number = 0, // FRONTIER
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = std::nullopt,
        .withdrawals_root = 0x00_bytes32};

    auto const result1 =
        static_validate_header<EvmTraits<EVMC_FRONTIER>>(header1);
    EXPECT_EQ(result1.error(), BlockError::FieldBeforeFork);

    static BlockHeader const header2{
        .ommers_hash = NULL_LIST_HASH,
        .number = 17034870, // SHANGHAI
        .gas_limit = 10000,
        .gas_used = 5000,
        .timestamp = 1681338455, // SHANGHAI
        .base_fee_per_gas = 1000,
        .withdrawals_root = std::nullopt};

    auto const result2 =
        static_validate_header<EvmTraits<EVMC_SHANGHAI>>(header2);
    EXPECT_EQ(result2.error(), BlockError::MissingField);
}

TEST(Validation, invalid_nonce)
{
    static constexpr byte_string_fixed<8> nonce{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08};

    static BlockHeader const header{
        .gas_limit = 10000,
        .gas_used = 5000,
        .nonce = nonce,
        .base_fee_per_gas = 1000};

    auto const result = static_validate_header<EvmTraits<EVMC_PARIS>>(header);
    EXPECT_EQ(result.error(), BlockError::InvalidNonce);
}
