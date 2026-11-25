// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <filesystem>
#include <fstream>
#include <limits>

using namespace monad;

namespace
{
    using NativeTraits = MonadTraits<MONAD_TEN>;

    Transaction transaction(size_t index = 1)
    {
        std::ifstream file(
            std::filesystem::path{__FILE__}.parent_path() /
            "monad_type40_vectors.json");
        auto const json = nlohmann::json::parse(file);
        auto const bytes =
            from_hex(json["vectors"][index]["canonical"].get<std::string>())
                .value();
        byte_string_view view{bytes};
        return rlp::decode_transaction(view).value();
    }

    template <Traits T = NativeTraits>
    Result<void> validate(Transaction const &tx, uint256_t chain = 20143)
    {
        return static_validate_transaction<T>(
            tx, 1, std::nullopt, chain, default_blob_schedule<T>());
    }
}

TEST(MonadValidation, ActivationRequiresMonadPragueRules)
{
    auto tx = transaction();
    EXPECT_TRUE(validate(tx).has_value());
    EXPECT_TRUE(validate<MonadTraits<MONAD_EIGHT>>(tx).has_value());
    EXPECT_TRUE(validate<MonadTraits<MONAD_NEXT>>(tx).has_value());
    EXPECT_EQ(
        validate<MonadTraits<MONAD_TWO>>(tx).error(),
        TransactionError::TypeNotSupported);
    EXPECT_EQ(
        validate<EvmTraits<EvmRevision::Prague>>(tx).error(),
        TransactionError::TypeNotSupported);
    EXPECT_EQ(
        validate<EvmTraits<EvmRevision::Amsterdam>>(tx).error(),
        TransactionError::TypeNotSupported);
    tx.type = static_cast<TransactionType>(0x41);
    EXPECT_EQ(validate(tx).error(), TransactionError::TypeNotSupported);
    tx.type = TransactionType::monad;
    tx.sc.chain_id = 143;
    EXPECT_TRUE(validate(tx, 143).has_value());
    EXPECT_EQ(validate(tx).error(), TransactionError::WrongChainId);
    tx.sc.chain_id.reset();
    EXPECT_EQ(validate(tx).error(), TransactionError::TypeNotSupported);
}

TEST(MonadValidation, NativeFeesUseUint128AndDynamicPricing)
{
    auto tx = transaction();
    tx.max_fee_per_gas = (uint256_t{1} << 128) - 1;
    tx.max_priority_fee_per_gas = tx.max_fee_per_gas - 1;
    EXPECT_TRUE(validate(tx).has_value());
    EXPECT_EQ(gas_price<NativeTraits>(tx, 1), tx.max_priority_fee_per_gas + 1);
    tx.max_fee_per_gas = 100;
    tx.max_priority_fee_per_gas = 101;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::PriorityFeeGreaterThanMax);
    tx.max_priority_fee_per_gas = 1;
    tx.max_fee_per_gas = uint256_t{1} << 128;
    EXPECT_EQ(validate(tx).error(), TransactionError::NativeQuantityOverflow);
    tx = transaction(6);
    EXPECT_EQ(validate(tx).error(), TransactionError::NonceExceedsMax);
}

TEST(MonadValidation, BatchIntrinsicChargesAllDataAndAccessListBytes)
{
    auto tx = transaction();
    tx.to.reset();
    tx.value = 0;
    tx.data.clear();
    tx.access_list = {{.a = Address{}, .keys = {bytes32_t{}}}};
    tx.calls = std::vector<TransactionCall>{
        {.to = Address{}, .data = byte_string{0, 1}},
        {.to = Address{}, .data = byte_string{2}}};
    auto const expected =
        21'000 + 21'000 + 4 + 32 + 2'400 + 1'900 + 40 * (20 + 32);
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), expected);
    EXPECT_EQ(
        floor_data_gas<NativeTraits>(tx), 21'000 + 10 + 80 + 40 * (20 + 32));
    tx.gas_limit = expected;
    EXPECT_TRUE(validate(tx).has_value());
    --tx.gas_limit;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::IntrinsicGasGreaterThanLimit);
    tx.calls->front().to.reset();
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), expected + 32'000 + 2);
}

TEST(MonadValidation, ExistingAccessListCreationAndCalldataGasApply)
{
    auto tx = transaction(3);
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), 25300);
    EXPECT_TRUE(validate(tx).has_value());
    --tx.gas_limit;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::IntrinsicGasGreaterThanLimit);
    tx = transaction(4);
    EXPECT_TRUE(validate(tx).has_value());
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), 53058);
    tx = transaction();
    tx.data = byte_string(226, 0x01);
    tx.gas_limit = 30000;
    EXPECT_EQ(floor_data_gas<NativeTraits>(tx), 30040);
    EXPECT_EQ(
        validate(tx).error(), TransactionError::IntrinsicGasGreaterThanLimit);
}

TEST(MonadValidation, NativeBoundsDoNotChangeDecoderOrEthereumValidation)
{
    // The preserved SDK fixture remains structurally decodable but no longer
    // executable.
    auto tx = transaction(5);
    EXPECT_EQ(validate(tx).error(), TransactionError::NativeQuantityOverflow);
    tx.type = TransactionType::eip1559;
    EXPECT_TRUE(validate(tx).has_value());

    tx = transaction();
    tx.max_priority_fee_per_gas = uint256_t{1} << 128;
    EXPECT_EQ(validate(tx).error(), TransactionError::NativeQuantityOverflow);
    tx.max_priority_fee_per_gas = 1;
    tx.sc.chain_id = std::numeric_limits<uint64_t>::max();
    EXPECT_EQ(validate(tx).error(), TransactionError::WrongChainId);
    tx.sc.chain_id = uint256_t{1} << 64;
    EXPECT_EQ(validate(tx).error(), TransactionError::NativeQuantityOverflow);
    tx = transaction(7);
    EXPECT_EQ(validate(tx).error(), TransactionError::NativeQuantityOverflow);
}

TEST(MonadValidation, BatchIntrinsicAndFloorIncludeAllSignedInputs)
{
    auto tx = transaction();
    tx.to.reset();
    tx.value = 0;
    tx.data.clear();
    tx.calls = std::vector<TransactionCall>{
        {.data = byte_string{0, 1, 0}},
        {.to = Address{}, .value = 1, .data = byte_string{2, 0}}};
    tx.access_list = {{.a = Address{}, .keys = {bytes32_t{}}}};
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), 80'426);
    EXPECT_EQ(floor_data_gas<NativeTraits>(tx), 23'190);
    tx.gas_limit = 80'425;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::IntrinsicGasGreaterThanLimit);
    tx.gas_limit = 80'426;
    EXPECT_TRUE(validate(tx).has_value());

    tx.calls->front().to = Address{};
    tx.calls->front().data.clear();
    tx.calls->back().data = byte_string(10'000, 1);
    tx.access_list.clear();
    EXPECT_EQ(intrinsic_gas<NativeTraits>(tx), 202'000);
    EXPECT_EQ(floor_data_gas<NativeTraits>(tx), 421'000);
    tx.gas_limit = 420'999;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::IntrinsicGasGreaterThanLimit);
    tx.gas_limit = 421'000;
    EXPECT_TRUE(validate(tx).has_value());
}
