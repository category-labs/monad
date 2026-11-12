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
    using NativeTraits = MonadTraits<MONAD_NINE>;

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

TEST(MonadValidation, ActivationIsDevnetAndPragueOnly)
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
    EXPECT_EQ(validate(tx, 143).error(), TransactionError::TypeNotSupported);
    EXPECT_EQ(validate(tx).error(), TransactionError::WrongChainId);
    tx.sc.chain_id.reset();
    EXPECT_EQ(validate(tx).error(), TransactionError::TypeNotSupported);
}

TEST(MonadValidation, NativeFeesUseFullWidthAndDynamicPricing)
{
    auto tx = transaction(5);
    EXPECT_TRUE(validate(tx).has_value());
    EXPECT_EQ(gas_price<NativeTraits>(tx, 1), tx.max_priority_fee_per_gas + 1);
    tx.max_priority_fee_per_gas = tx.max_fee_per_gas + 1;
    EXPECT_EQ(
        validate(tx).error(), TransactionError::PriorityFeeGreaterThanMax);
    tx.max_priority_fee_per_gas = 1;
    tx.max_fee_per_gas = std::numeric_limits<uint256_t>::max();
    EXPECT_EQ(validate(tx).error(), TransactionError::GasLimitOverflow);
    tx = transaction(6);
    EXPECT_EQ(validate(tx).error(), TransactionError::NonceExceedsMax);
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
