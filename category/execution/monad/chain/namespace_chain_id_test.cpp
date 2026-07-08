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

#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/execution/monad/chain/namespace_chain_id.hpp>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

namespace
{
    constexpr uint64_t NETWORK_CHAIN_ID = 10143;

    Transaction valid_transaction(uint256_t const &chain_id)
    {
        return Transaction{
            .sc =
                SignatureAndChain{
                    .signature = {.r = 1, .s = 1, .y_parity = 0},
                    .chain_id = chain_id,
                },
            .max_fee_per_gas = 1,
            .gas_limit = 27'500,
            .to = Address{1}};
    }
}

TEST(NamespaceChainId, network_chain_id_has_no_namespace)
{
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};

    auto const result =
        namespace_from_chain_id(network_chain_id, network_chain_id);

    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result.value().has_value());
}

TEST(NamespaceChainId, matching_suffix_returns_namespace_id)
{
    uint64_t const namespace_id = (uint64_t{0x1234} << 16) | NETWORK_CHAIN_ID;
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};

    auto const result =
        namespace_from_chain_id(uint256_t{namespace_id}, network_chain_id);

    ASSERT_TRUE(result.has_value());
    ASSERT_TRUE(result.value().has_value());
    EXPECT_EQ(*result.value(), namespace_id);
}

TEST(NamespaceChainId, mismatched_suffix_is_wrong_chain_id)
{
    uint64_t const namespace_id =
        (uint64_t{0x1234} << 16) | (NETWORK_CHAIN_ID + 1);
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};

    auto const result =
        namespace_from_chain_id(uint256_t{namespace_id}, network_chain_id);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::WrongChainId);
}

TEST(NamespaceChainId, over_u64_chain_id_is_wrong_chain_id)
{
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};
    uint256_t const chain_id =
        (uint256_t{1} << 64) | uint256_t{NETWORK_CHAIN_ID};

    auto const result = namespace_from_chain_id(chain_id, network_chain_id);

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::WrongChainId);
}

TEST(NamespaceChainId, static_validation_accepts_namespace_at_monad_next)
{
    using Traits = MonadTraits<MONAD_NEXT>;
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};
    uint256_t const namespace_id =
        uint256_t{(uint64_t{0x1234} << 16) | NETWORK_CHAIN_ID};
    Transaction const tx = valid_transaction(namespace_id);

    auto const result = static_validate_transaction<Traits>(
        tx, 0, std::nullopt, network_chain_id, default_blob_schedule<Traits>());

    EXPECT_TRUE(result.has_value());
}

TEST(NamespaceChainId, static_validation_rejects_namespace_before_monad_next)
{
    using Traits = MonadTraits<MONAD_FOUR>;
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};
    uint256_t const namespace_id =
        uint256_t{(uint64_t{0x1234} << 16) | NETWORK_CHAIN_ID};
    Transaction const tx = valid_transaction(namespace_id);

    auto const result = static_validate_transaction<Traits>(
        tx, 0, std::nullopt, network_chain_id, default_blob_schedule<Traits>());

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::WrongChainId);
}

TEST(NamespaceChainId, static_validation_rejects_bad_namespace_suffix)
{
    using Traits = MonadTraits<MONAD_NEXT>;
    uint256_t const network_chain_id{NETWORK_CHAIN_ID};
    uint256_t const namespace_id =
        uint256_t{(uint64_t{0x1234} << 16) | (NETWORK_CHAIN_ID + 1)};
    Transaction const tx = valid_transaction(namespace_id);

    auto const result = static_validate_transaction<Traits>(
        tx, 0, std::nullopt, network_chain_id, default_blob_schedule<Traits>());

    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::WrongChainId);
}
