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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/test/test_traits_state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <type_traits>

using namespace monad;

namespace
{
    using namespace ::monad::literals;

    static constexpr auto r{
        0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256};
    static constexpr auto s{
        0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256};

    template <monad_eth_revision r>
    using rev = std::integral_constant<monad_eth_revision, r>;

    static constexpr auto sender =
        0x000000000000000000000000000000000000000a_address;

    static constexpr auto to =
        0x5353535353535353535353535353535353535353_address;
}

TYPED_TEST(TraitsTest, validate_enough_gas)
{
    static_assert(TestFixture::Trait::evm_rev() >= MONAD_ETH_HOMESTEAD);

    static Transaction const t{
        .sc = {.signature = {.r = r, .s = s}},
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .value = 1};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t,
            0,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::IntrinsicGasGreaterThanLimit);
}

TYPED_TEST(TraitsTest, validate_floor_gas)
{
    static_assert(TestFixture::Trait::evm_rev() >= MONAD_ETH_ISTANBUL);

    static constexpr auto gas_limit = 300'000;
    Transaction const t{
        .sc = {.signature = {.r = r, .s = s}},
        .gas_limit = gas_limit,
        .data = evmc::bytes(10000, 0x01),
    };

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t,
            0,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());

    if constexpr (TestFixture::Trait::evm_rev() >= MONAD_ETH_PRAGUE) {
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
    if constexpr (TestFixture::Trait::evm_rev() >= MONAD_ETH_PRAGUE) {
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

TYPED_TEST(InMemoryStateTraitsTest, successful_validation)
{
    this->state.add_to_balance(sender, 56'939'568'773'815'811);
    this->state.set_nonce(sender, 25);
    Transaction const tx{
        .sc = {.signature = {.r = r, .s = s}},
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 55'939'568'773'815'811,
        .to = to};

    auto const result1 =
        static_validate_transaction<typename TestFixture::Trait>(
            tx,
            0,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());
    EXPECT_TRUE(result1.has_value());

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result2 =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
    EXPECT_TRUE(result2.has_value());
}

TYPED_TEST(TraitsTest, invalid_signature)
{
    // A transaction that passes every earlier static check but carries a bad
    // r/s must be rejected with InvalidSignature (EIP-2).
    static Transaction const t{
        .sc = {.signature = {.r = 0, .s = s}},
        .nonce = 25,
        .max_fee_per_gas = 29'443'849'433,
        .gas_limit = 27'500,
        .value = 1,
        .to = to};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t,
            0,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InvalidSignature);
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
            t,
            37'000'000'000,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());
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
            t,
            29'000'000'000,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());
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

    trace::StateTracer noop_state_tracer = std::monostate{};
    auto const result =
        validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, sender, this->state, noop_state_tracer);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
}

// EIP-3860
TYPED_TEST(TraitsTest, init_code_exceed_limit)
{
    static_assert(TestFixture::Trait::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

    byte_string long_data;
    for (auto i = 0u; i <= 2 * TestFixture::Trait::max_code_size(); ++i) {
        long_data += {0xc0};
    }
    // exceed EIP-3860 limit

    static Transaction const t{
        .sc = {.signature = {.r = r, .s = s}},
        .max_fee_per_gas = 0,
        .gas_limit = 20'000'000,
        .value = 0,
        .data = long_data};

    auto const result =
        static_validate_transaction<typename TestFixture::Trait>(
            t,
            0,
            std::nullopt,
            1,
            default_blob_schedule<typename TestFixture::Trait>());
    // init codesize validation since EIP-3860
    if constexpr (TestFixture::Trait::evm_rev() >= MONAD_ETH_SHANGHAI) {
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), TransactionError::InitCodeLimitExceeded);
    }
    else {
        EXPECT_TRUE(result.has_value());
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

TYPED_TEST(TraitsTest, header_gas_used_above_limit)
{
    BlockHeader const header{.gas_limit = 5000, .gas_used = 5001};

    auto const result =
        static_validate_header<typename TestFixture::Trait>(header);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), BlockError::GasAboveLimit);
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
    auto value_since = []<monad_eth_revision rev, typename T>(
                           std::integral_constant<monad_eth_revision, rev>,
                           T val) consteval {
        if constexpr (TestFixture::Trait::evm_rev() >= rev) {
            return std::optional<T>{val};
        }
        else {
            return std::nullopt;
        }
    };

    static constexpr auto base_fee_per_gas =
        value_since(rev<MONAD_ETH_LONDON>{}, uint256_t{});
    static constexpr auto withdrawals_root =
        value_since(rev<MONAD_ETH_SHANGHAI>{}, bytes32_t{});
    static constexpr auto blob_gas_used =
        value_since(rev<MONAD_ETH_CANCUN>{}, uint64_t{});
    static constexpr auto excess_blob_gas =
        value_since(rev<MONAD_ETH_CANCUN>{}, uint64_t{});
    static constexpr auto parent_beacon_block_root =
        value_since(rev<MONAD_ETH_CANCUN>{}, bytes32_t{});
    static constexpr auto requests_hash =
        value_since(rev<MONAD_ETH_PRAGUE>{}, bytes32_t{});

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

    TEST_OPTIONAL_FIELD(base_fee_per_gas, uint256_t{}, MONAD_ETH_LONDON)
    TEST_OPTIONAL_FIELD(withdrawals_root, bytes32_t{}, MONAD_ETH_SHANGHAI)
    TEST_OPTIONAL_FIELD(blob_gas_used, uint64_t{}, MONAD_ETH_CANCUN)
    TEST_OPTIONAL_FIELD(excess_blob_gas, uint64_t{}, MONAD_ETH_CANCUN)
    TEST_OPTIONAL_FIELD(parent_beacon_block_root, bytes32_t{}, MONAD_ETH_CANCUN)
    TEST_OPTIONAL_FIELD(requests_hash, bytes32_t{}, MONAD_ETH_PRAGUE)
}

#undef TEST_OPTIONAL_FIELD

TYPED_TEST(TraitsTest, calc_excess_blob_gas)
{
    auto const target_blob_gas =
        target_blob_gas_per_block(CANCUN_BLOB_SCHEDULE);

    BlockHeader parent{
        .blob_gas_used = target_blob_gas + GAS_PER_BLOB,
        .excess_blob_gas = target_blob_gas};

    EXPECT_EQ(
        calc_excess_blob_gas<typename TestFixture::Trait>(
            parent, CANCUN_BLOB_SCHEDULE),
        target_blob_gas + GAS_PER_BLOB);

    parent.blob_gas_used = 0;
    parent.excess_blob_gas = target_blob_gas - 1;
    EXPECT_EQ(
        calc_excess_blob_gas<typename TestFixture::Trait>(
            parent, CANCUN_BLOB_SCHEDULE),
        0);
}

TYPED_TEST(TraitsTest, calc_excess_blob_gas_uses_reserve_price_when_active)
{
    BlobSchedule const blob_schedule = PRAGUE_BLOB_SCHEDULE;
    auto const target_blob_gas = target_blob_gas_per_block(blob_schedule);

    BlockHeader parent{
        .base_fee_per_gas = uint256_t{1'000'000},
        .blob_gas_used = target_blob_gas,
        .excess_blob_gas = target_blob_gas};

    uint64_t const expected_excess_blob_gas = [&] {
        if constexpr (TestFixture::Trait::eip_7918_active()) {
            return target_blob_gas +
                   target_blob_gas *
                       (blob_schedule.max_blobs_per_block -
                        blob_schedule.target_blobs_per_block) /
                       blob_schedule.max_blobs_per_block;
        }
        else {
            return target_blob_gas;
        }
    }();

    EXPECT_EQ(
        calc_excess_blob_gas<typename TestFixture::Trait>(
            parent, blob_schedule),
        expected_excess_blob_gas);
}

TYPED_TEST(TraitsTest, validate_excess_blob_gas_against_parent)
{
    if constexpr (!TestFixture::Trait::eip_4844_active()) {
        GTEST_SKIP() << "EIP-4844 is not active";
    }
    else {
        static constexpr uint64_t timestamp =
            TestFixture::Trait::evm_rev() >= MONAD_ETH_PRAGUE
                ? uint64_t{1746612311}
                : uint64_t{1710338135};

        EthereumMainnet const chain;
        auto const blob_schedule = chain.get_blob_schedule(timestamp);
        auto const target_blob_gas = target_blob_gas_per_block(blob_schedule);

        BlockHeader parent{
            .gas_limit = 10000,
            .base_fee_per_gas = uint256_t{},
            .blob_gas_used = target_blob_gas + GAS_PER_BLOB,
            .excess_blob_gas = target_blob_gas};
        uint64_t const expected_excess_blob_gas =
            calc_excess_blob_gas<typename TestFixture::Trait>(
                parent, blob_schedule);

        BlockHeader header{
            .number = 1,
            .gas_limit = 10000,
            .timestamp = timestamp,
            .base_fee_per_gas = uint256_t{},
            .withdrawals_root = bytes32_t{},
            .blob_gas_used = uint64_t{0},
            .excess_blob_gas = expected_excess_blob_gas,
            .parent_beacon_block_root = bytes32_t{}};
        if constexpr (TestFixture::Trait::evm_rev() >= MONAD_ETH_PRAGUE) {
            header.requests_hash = bytes32_t{};
        }
        Block block{.header = header, .withdrawals = std::vector<Withdrawal>{}};

        auto result = static_validate_ethereum_block_with_parent<
            typename TestFixture::Trait>(chain, block, parent);
        EXPECT_TRUE(result.has_value());

        block.header.excess_blob_gas = expected_excess_blob_gas + 1;
        result = static_validate_ethereum_block_with_parent<
            typename TestFixture::Trait>(chain, block, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidExcessBlobGas);
    }
}

// A parent every rule below accepts: the gas used sits exactly on the
// elasticity target, so the EIP-1559 formula reproduces its own base fee.
static BlockHeader parent_for_header_rules()
{
    return BlockHeader{
        .gas_limit = 30'000'000,
        .gas_used = 15'000'000,
        .timestamp = 1000,
        .base_fee_per_gas = uint256_t{1'000'000'000}};
}

static BlockHeader child_of(BlockHeader const &parent)
{
    return BlockHeader{
        .gas_limit = parent.gas_limit,
        .timestamp = parent.timestamp + 12,
        .base_fee_per_gas = parent.base_fee_per_gas};
}

TYPED_TEST(TraitsTest, header_timestamp_strictly_after_parent)
{
    BlockHeader const parent = parent_for_header_rules();
    BlockHeader header = child_of(parent);

    EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                    typename TestFixture::Trait>(header, parent)
                    .has_value());

    for (uint64_t const t : {parent.timestamp, parent.timestamp - 1}) {
        header.timestamp = t;
        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidTimestamp);
    }
}

TYPED_TEST(TraitsTest, header_gas_limit_within_a_1024th_of_parent)
{
    BlockHeader const parent = parent_for_header_rules();
    BlockHeader header = child_of(parent);
    uint64_t const bound = parent.gas_limit / 1024;

    // The bound is exclusive on both sides.
    for (uint64_t const g :
         {parent.gas_limit + bound - 1, parent.gas_limit - bound + 1}) {
        header.gas_limit = g;
        EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                        typename TestFixture::Trait>(header, parent)
                        .has_value());
    }
    for (uint64_t const g :
         {parent.gas_limit + bound, parent.gas_limit - bound}) {
        header.gas_limit = g;
        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidGasLimit);
    }
}

TYPED_TEST(TraitsTest, header_base_fee_recomputed_from_parent)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_LONDON) {
        GTEST_SKIP() << "EIP-1559 is not active";
    }
    else {
        BlockHeader const parent = parent_for_header_rules();
        BlockHeader header = child_of(parent);

        EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                        typename TestFixture::Trait>(header, parent)
                        .has_value());

        header.base_fee_per_gas = parent.base_fee_per_gas.value() + 1;
        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidBaseFeePerGas);
    }
}

TYPED_TEST(TraitsTest, header_with_parent_missing_base_fee)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_LONDON) {
        GTEST_SKIP() << "EIP-1559 is not active";
    }
    else {
        BlockHeader const parent = parent_for_header_rules();
        BlockHeader header = child_of(parent);
        header.base_fee_per_gas = std::nullopt;

        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::MissingField);
    }
}

TYPED_TEST(TraitsTest, header_base_fee_wide_arithmetic)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_LONDON) {
        GTEST_SKIP() << "EIP-1559 is not active";
    }
    else {
        BlockHeader parent = parent_for_header_rules();
        parent.base_fee_per_gas = (uint256_t{1} << 240) + 7;
        BlockHeader header = child_of(parent);
        auto const fee = parent.base_fee_per_gas.value();

        // Full and empty blocks change the fee by floor(fee / 8).
        // Both products overflow 256 bits, but both final fees fit.
        for (bool const increasing : {false, true}) {
            parent.gas_used = increasing ? parent.gas_limit : 0;
            header.base_fee_per_gas =
                increasing ? fee + fee / 8 : fee - fee / 8;
            EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                            typename TestFixture::Trait>(header, parent)
                            .has_value());

            auto const target = parent.gas_limit / 2;
            auto const wrapped_delta = fee * uint256_t{target} / target / 8;
            header.base_fee_per_gas =
                increasing ? fee + wrapped_delta : fee - wrapped_delta;
            auto const result = static_validate_ethereum_header_with_parent<
                typename TestFixture::Trait>(header, parent);
            ASSERT_TRUE(result.has_error());
            EXPECT_EQ(result.error(), BlockError::InvalidBaseFeePerGas);
        }

        // A one-wei fee still increases by at least one wei.
        parent.base_fee_per_gas = uint256_t{1};
        parent.gas_used = parent.gas_limit / 2 + 1;
        header.base_fee_per_gas = uint256_t{2};
        EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                        typename TestFixture::Trait>(header, parent)
                        .has_value());

        // Reject overflow of the final addition, including its wrapped value.
        parent.base_fee_per_gas = std::numeric_limits<uint256_t>::max();
        parent.gas_used = parent.gas_limit;
        auto const max_fee = parent.base_fee_per_gas.value();
        header.base_fee_per_gas = max_fee + max_fee / 8;
        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidBaseFeePerGas);

        // An unchecked parent can also produce a delta wider than 256 bits.
        parent.gas_used = std::numeric_limits<uint64_t>::max();
        auto const oversized = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(oversized.has_error());
        EXPECT_EQ(oversized.error(), BlockError::InvalidBaseFeePerGas);
    }
}

TYPED_TEST(TraitsTest, header_at_london_activation)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_LONDON) {
        GTEST_SKIP() << "EIP-1559 is not active";
    }
    else {
        // A pre-London parent: no base fee, and a gas limit that doubles.
        BlockHeader parent = parent_for_header_rules();
        parent.base_fee_per_gas = std::nullopt;

        BlockHeader header{
            .gas_limit = parent.gas_limit * 2,
            .timestamp = parent.timestamp + 12,
            .base_fee_per_gas = uint256_t{1'000'000'000}};
        EXPECT_TRUE(static_validate_ethereum_header_with_parent<
                        typename TestFixture::Trait>(header, parent)
                        .has_value());

        // Measured against the parent's own limit it would be refused.
        header.gas_limit = parent.gas_limit;
        auto const result = static_validate_ethereum_header_with_parent<
            typename TestFixture::Trait>(header, parent);
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidGasLimit);
    }
}

TYPED_TEST(TraitsTest, invalid_nonce)
{
    auto value_since = []<monad_eth_revision rev, typename T>(
                           std::integral_constant<monad_eth_revision, rev>,
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
        value_since(rev<MONAD_ETH_LONDON>{}, uint256_t{});
    static constexpr auto withdrawals_root =
        value_since(rev<MONAD_ETH_SHANGHAI>{}, bytes32_t{});
    static constexpr auto blob_gas_used =
        value_since(rev<MONAD_ETH_CANCUN>{}, uint64_t{});
    static constexpr auto excess_blob_gas =
        value_since(rev<MONAD_ETH_CANCUN>{}, uint64_t{});
    static constexpr auto parent_beacon_block_root =
        value_since(rev<MONAD_ETH_CANCUN>{}, bytes32_t{});
    static constexpr auto requests_hash =
        value_since(rev<MONAD_ETH_PRAGUE>{}, bytes32_t{});

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
    if constexpr (TestFixture::Trait::evm_rev() >= MONAD_ETH_PARIS) {
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), BlockError::InvalidNonce);
    }
    else {
        EXPECT_TRUE(result.has_value());
    }
}
