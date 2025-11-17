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
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <monad/test/traits_test.hpp>

#include <vector>

#include <gtest/gtest.h>

using namespace monad;

TYPED_TEST(MonadTraitsTest, no_system_txns)
{
    std::vector<Address> senders{
        0xaaaa_address,
        0xbbbb_address,
        0xcccc_address,
    };
    std::vector<Transaction> txns(senders.size());
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    EXPECT_FALSE(res.has_error());
}

TYPED_TEST(MonadTraitsTest, multiple_system_txns_ok)
{
    std::vector<Address> senders{
        SYSTEM_SENDER,
        SYSTEM_SENDER,
        0xaaaa_address,
        0xbbbb_address,
    };
    std::vector<Transaction> txns(senders.size());
    txns[1].value = 25 * staking::MON;
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    EXPECT_FALSE(res.has_error());
}

TYPED_TEST(MonadTraitsTest, system_txn_comes_after_user_txn)
{
    using Trait = typename TestFixture::Trait;

    std::vector<Address> senders{
        0xaaaa_address,
        0xbbbb_address,
        SYSTEM_SENDER,
        0xcccc_address,
    };
    std::vector<Transaction> txns(senders.size());
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    if constexpr (Trait::monad_rev() < MONAD_FOUR) {
        EXPECT_FALSE(res.has_error());
    }
    else {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(
            res.error(), MonadBlockError::SystemTransactionNotFirstInBlock);
    }
}

TYPED_TEST(MonadTraitsTest, multiple_reward_txns_error)
{
    using Trait = typename TestFixture::Trait;

    std::vector<Address> senders{
        SYSTEM_SENDER,
        SYSTEM_SENDER,
        0xaaaa_address,
        0xbbbb_address,
    };
    std::vector<Transaction> txns(senders.size());
    txns[0].value = 25 * staking::MON;
    txns[1].value = 1 * staking::MON;
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    if constexpr (Trait::monad_rev() < MONAD_FOUR) {
        EXPECT_FALSE(res.has_error());
    }
    else {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), MonadBlockError::MultipleRewardTransactions);
    }
}

TYPED_TEST(MonadTraitsTest, reward_txn_exceeds_maximum)
{
    using Trait = typename TestFixture::Trait;

    std::vector<Address> senders{
        SYSTEM_SENDER,
        0xaaaa_address,
    };
    std::vector<Transaction> txns(senders.size());
    txns[0].value = 26 * staking::MON;
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    if constexpr (Trait::monad_rev() < MONAD_FOUR) {
        EXPECT_FALSE(res.has_error());
    }
    else {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), MonadBlockError::InvalidRewardValue);
    }
}
