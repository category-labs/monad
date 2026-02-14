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
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/dao.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/test/test_traits_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>

using namespace monad;

namespace
{
    using namespace ::monad::literals;
    using intx::operator""_u256;

    static constexpr auto r{
        0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256};
    static constexpr auto s{
        0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256};

    template <evmc_revision r>
    using rev = std::integral_constant<evmc_revision, r>;

    static constexpr auto sender =
        0x000000000000000000000000000000000000000a_address;

    static constexpr auto to =
        0x5353535353535353535353535353535353535353_address;
}

TYPED_TEST(TraitsTest, validate_enough_gas)
{
    static Transaction const t{
        .sc = {.r = r, .s = s},
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t, 0, std::nullopt, 1);

    if constexpr (TestFixture::Trait::evm_rev() == EVMC_FRONTIER) {
        EXPECT_TRUE(result.has_value());
    }
    else {
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
    }
}

TYPED_TEST(TraitsTest, validate_floor_gas)
{
    static constexpr auto gas_limit = [] {
        // intrinsic gas requirement was much higher pre Istanbul due to 68 gas
        // cost per non-zero data vs 16 gas post Istanbul
        if constexpr (TestFixture::Trait::evm_rev() >= EVMC_ISTANBUL) {
            return 300'000;
        }
        else {
            return 800'000;
        }
    }();
    Transaction const t{
        .sc = {.r = r, .s = s},
        .gas_limit = gas_limit,
        .data = evmc::bytes(10000, 0x01),
    };

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t, 0, std::nullopt, 1);

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        // Floor gas only introduced since Prague
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
    }
    else {
        EXPECT_TRUE(result.has_value());
    }
}

TYPED_TEST(InMemoryStateTraitsTest, validate_deployed_code)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_nonce(sender, 24);
    this->state.set_code(sender, 0x00_bytes);
    Transaction const tx{.gas_limit = 60'500};

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::SenderNotEoa);
}

// EIP-7702
TYPED_TEST(InMemoryStateTraitsTest, validate_deployed_code_delegated)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_code(
        sender, 0xEF01001122334455112233445511223344551122334455_bytes);
    Transaction const tx{.gas_limit = 60'500};

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        EXPECT_TRUE(result.has_value());
    }
    else {
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), TransactionError::SenderNotEoa);
    }
}

TYPED_TEST(InMemoryStateTraitsTest, validate_nonce)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_nonce(sender, 24);
    Transaction const tx{
        .nonce = 23,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
}

TYPED_TEST(InMemoryStateTraitsTest, validate_nonce_optimistically)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_nonce(sender, 24);
    Transaction const tx{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 60'500,
        .value = 55'939'568'773'815'811};

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::BadNonce);
}

TYPED_TEST(InMemoryStateTraitsTest, validate_enough_balance)
{
    this->state.add_to_balance(sender, 55'939'568'773'815'811);
    Transaction const tx{
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = to,
        .max_priority_fee_per_gas = 100'000'000,
    };

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

TYPED_TEST(InMemoryStateTraitsTest, successful_validation)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_nonce(sender, 25);
    Transaction const tx{
        .sc = {.r = r, .s = s},
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = to};

    auto const result1 =
        static_validate_transaction<typename TestFixture::Trait>(
            tx, 0, std::nullopt, 1);
    EXPECT_TRUE(result1.has_value());

    auto const result2 =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    EXPECT_TRUE(result2.has_value());
}

TYPED_TEST(TraitsTest, max_fee_less_than_base)
{
    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = to,
        .max_priority_fee_per_gas = 100'000'000};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t, 37'000'000'000, std::nullopt, 1);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::MaxFeeLessThanBase);
}

TYPED_TEST(TraitsTest, priority_fee_greater_than_max)
{
    static Transaction const t{
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 48'979'750'000'000'000,
        .to = to,
        .max_priority_fee_per_gas = 100'000'000'000};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t, 29'000'000'000, std::nullopt, 1);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::PriorityFeeGreaterThanMax);
}

TYPED_TEST(InMemoryStateTraitsTest, insufficent_balance_overflow)
{
    this->state.add_to_balance(sender, std::numeric_limits<uint256_t>::max());
    Transaction const tx{
        .max_fee_per_gas = std::numeric_limits<uint256_t>::max() - 1,
        .gas_limit = 1000,
        .value = 0,
        .to = to};

    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

// EIP-3860
TYPED_TEST(TraitsTest, init_code_exceed_limit)
{
    // Before Spurious Dragon, max_code_size is uncapped
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SPURIOUS_DRAGON) {
        byte_string long_data;
        for (auto i = 0u; i <= 2 * TestFixture::Trait::max_code_size(); ++i) {
            long_data += {0xc0};
        }
        // exceed EIP-3860 limit

        static Transaction const t{
            .sc = {.r = r, .s = s},
            .max_fee_per_gas = 0,
            .gas_limit = 20'000'000,
            .value = 0,
            .data = long_data};

        auto const result =
            static_validate_transaction<typename TestFixture::Trait>(
                t, 0, std::nullopt, 1);
        // init codesize validation since EIP-3860
        if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {
            ASSERT_TRUE(result.has_error());
            EXPECT_EQ(result.error(), TransactionError::InitCodeLimitExceeded);
        }
        else {
            EXPECT_TRUE(result.has_value());
        }
    }
    else {
        static_assert(
            TestFixture::Trait::max_code_size() ==
            std::numeric_limits<size_t>::max());
    }
}

TYPED_TEST(TraitsTest, invalid_gas_limit)
{
    static BlockHeader const header{.gas_limit = 1000, .gas_used = 500};

    auto const result =
        static_validate_header<typename TestFixture::Trait>(header);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), BlockError::InvalidGasLimit);
}

TYPED_TEST(EvmTraitsTest, wrong_dao_extra_data)
{
    static BlockHeader const header{
        .number = dao::dao_block_number + 5,
        .gas_limit = 10000,
        .extra_data = {0x00, 0x01, 0x02}};

    auto const result =
        static_validate_header<typename TestFixture::Trait>(header);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), BlockError::WrongDaoExtraData);
}

#define TEST_OPTIONAL_FIELD(f, default_val, REV)                               \
    {                                                                          \
        if constexpr (TestFixture::Trait::evm_rev() >= REV) {                  \
            static_assert(!!valid_header.f);                                   \
            BlockHeader invalid_header = valid_header;                         \
            invalid_header.f = std::nullopt;                                   \
            auto const result =                                                \
                static_validate_header<typename TestFixture::Trait>(           \
                    invalid_header);                                           \
            ASSERT_TRUE(result.has_error());                                   \
            EXPECT_EQ(result.error(), BlockError::MissingField);               \
        }                                                                      \
        else {                                                                 \
            static_assert(!valid_header.f);                                    \
            BlockHeader invalid_header = valid_header;                         \
            invalid_header.f = default_val;                                    \
            auto const result =                                                \
                static_validate_header<typename TestFixture::Trait>(           \
                    invalid_header);                                           \
            ASSERT_TRUE(result.has_error());                                   \
            EXPECT_EQ(result.error(), BlockError::FieldBeforeFork);            \
        }                                                                      \
    }

TYPED_TEST(TraitsTest, optional_fields_existence)
{
    auto value_since = []<evmc_revision rev, typename T>(
                           std::integral_constant<evmc_revision, rev>,
                           T val) consteval {
        if constexpr (TestFixture::Trait::evm_rev() >= rev) {
            return std::optional<T>{val};
        }
        else {
            return std::nullopt;
        }
    };

    static constexpr auto base_fee_per_gas =
        value_since(rev<EVMC_LONDON>{}, uint256_t{});
    static constexpr auto withdrawals_root =
        value_since(rev<EVMC_SHANGHAI>{}, bytes32_t{});
    static constexpr auto blob_gas_used =
        value_since(rev<EVMC_CANCUN>{}, uint64_t{});
    static constexpr auto excess_blob_gas =
        value_since(rev<EVMC_CANCUN>{}, uint64_t{});
    static constexpr auto parent_beacon_block_root =
        value_since(rev<EVMC_CANCUN>{}, bytes32_t{});
    static constexpr auto requests_hash =
        value_since(rev<EVMC_PRAGUE>{}, bytes32_t{});

    static constexpr BlockHeader valid_header{
        .gas_limit = 10000,
        .gas_used = 5000,
        .base_fee_per_gas = base_fee_per_gas,
        .withdrawals_root = withdrawals_root,
        .blob_gas_used = blob_gas_used,
        .excess_blob_gas = excess_blob_gas,
        .parent_beacon_block_root = parent_beacon_block_root,
        .requests_hash = requests_hash};

    EXPECT_TRUE(
        static_validate_header<typename TestFixture::Trait>(valid_header)
            .has_value());

    TEST_OPTIONAL_FIELD(base_fee_per_gas, uint256_t{}, EVMC_LONDON)
    TEST_OPTIONAL_FIELD(withdrawals_root, bytes32_t{}, EVMC_SHANGHAI)
    TEST_OPTIONAL_FIELD(blob_gas_used, uint64_t{}, EVMC_CANCUN)
    TEST_OPTIONAL_FIELD(excess_blob_gas, uint64_t{}, EVMC_CANCUN)
    TEST_OPTIONAL_FIELD(parent_beacon_block_root, bytes32_t{}, EVMC_CANCUN)
    TEST_OPTIONAL_FIELD(requests_hash, bytes32_t{}, EVMC_PRAGUE)
}

#undef TEST_OPTIONAL_FIELD

TYPED_TEST(TraitsTest, invalid_nonce)
{
    auto value_since = []<evmc_revision rev, typename T>(
                           std::integral_constant<evmc_revision, rev>,
                           T val) consteval {
        if constexpr (TestFixture::Trait::evm_rev() >= rev) {
            return std::optional<T>{val};
        }
        else {
            return std::nullopt;
        }
    };

    static constexpr byte_string_fixed<8> nonce{
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08};

    static constexpr auto base_fee_per_gas =
        value_since(rev<EVMC_LONDON>{}, uint256_t{});
    static constexpr auto withdrawals_root =
        value_since(rev<EVMC_SHANGHAI>{}, bytes32_t{});
    static constexpr auto blob_gas_used =
        value_since(rev<EVMC_CANCUN>{}, uint64_t{});
    static constexpr auto excess_blob_gas =
        value_since(rev<EVMC_CANCUN>{}, uint64_t{});
    static constexpr auto parent_beacon_block_root =
        value_since(rev<EVMC_CANCUN>{}, bytes32_t{});
    static constexpr auto requests_hash =
        value_since(rev<EVMC_PRAGUE>{}, bytes32_t{});

    static constexpr BlockHeader header{
        .gas_limit = 10000,
        .gas_used = 5000,
        .nonce = nonce,
        .base_fee_per_gas = base_fee_per_gas,
        .withdrawals_root = withdrawals_root,
        .blob_gas_used = blob_gas_used,
        .excess_blob_gas = excess_blob_gas,
        .parent_beacon_block_root = parent_beacon_block_root,
        .requests_hash = requests_hash};

    auto const result =
        static_validate_header<typename TestFixture::Trait>(header);
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PARIS) {
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidNonce);
    }
    else {
        EXPECT_TRUE(result.has_value());
    }
}
