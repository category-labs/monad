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
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <monad/test/traits_test.hpp>

#include <string_view>
#include <vector>

#include <gtest/gtest.h>

using namespace monad;
using staking::selector::ON_EPOCH_CHANGE;
using staking::selector::REWARD;
using staking::selector::SNAPSHOT;

namespace
{
    byte_string syscall_calldata(uint32_t const selector)
    {
        u32_be const be{selector};
        return byte_string{be.bytes, sizeof(be.bytes)};
    }

    std::vector<Address> system_senders(size_t const n)
    {
        return std::vector<Address>(n, SYSTEM_SENDER);
    }

    std::vector<Transaction> system_txns(std::vector<uint32_t> const &selectors)
    {
        std::vector<Transaction> txns(selectors.size());
        for (size_t i = 0; i < selectors.size(); ++i) {
            txns[i].data = syscall_calldata(selectors[i]);
        }
        return txns;
    }
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
    auto const res = static_validate_monad_body<Trait>(senders, txns);
    if constexpr (Trait::monad_rev() < MONAD_FOUR) {
        EXPECT_FALSE(res.has_error());
    }
    else {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(
            res.error(), MonadBlockError::SystemTransactionNotFirstInBlock);
    }
}

TYPED_TEST(MonadTraitsTest, system_txns_then_user_txns_ok)
{
    std::vector<Address> senders{
        SYSTEM_SENDER,
        SYSTEM_SENDER,
        0xaaaa_address,
        0xbbbb_address,
    };
    std::vector<Transaction> txns(senders.size());
    txns[0].data = syscall_calldata(SNAPSHOT);
    txns[1].data = syscall_calldata(REWARD);
    auto const res =
        static_validate_monad_body<typename TestFixture::Trait>(senders, txns);
    EXPECT_FALSE(res.has_error());
}

TYPED_TEST(MonadTraitsTest, valid_syscall_ordering)
{
    std::vector<std::vector<uint32_t>> const orders{
        {},
        {SNAPSHOT},
        {ON_EPOCH_CHANGE},
        {REWARD},
        {SNAPSHOT, ON_EPOCH_CHANGE},
        {SNAPSHOT, REWARD},
        {ON_EPOCH_CHANGE, REWARD},
        {SNAPSHOT, ON_EPOCH_CHANGE, REWARD},
    };

    for (auto const &order : orders) {
        auto const senders = system_senders(order.size());
        auto const txns = system_txns(order);
        auto const res =
            static_validate_monad_body<typename TestFixture::Trait>(
                senders, txns);
        EXPECT_FALSE(res.has_error());
    }
}

TYPED_TEST(MonadTraitsTest, invalid_syscall_ordering)
{
    using Trait = typename TestFixture::Trait;

    std::vector<std::vector<uint32_t>> const orders{
        {ON_EPOCH_CHANGE, SNAPSHOT},
        {REWARD, SNAPSHOT},
        {REWARD, ON_EPOCH_CHANGE},
        {SNAPSHOT, REWARD, ON_EPOCH_CHANGE},
        {ON_EPOCH_CHANGE, SNAPSHOT, REWARD},
        {ON_EPOCH_CHANGE, REWARD, SNAPSHOT},
        {REWARD, SNAPSHOT, ON_EPOCH_CHANGE},
        {REWARD, ON_EPOCH_CHANGE, SNAPSHOT},
    };

    for (auto const &order : orders) {
        auto const senders = system_senders(order.size());
        auto const txns = system_txns(order);
        auto const res = static_validate_monad_body<Trait>(senders, txns);
        if constexpr (Trait::monad_rev() < MONAD_FOUR) {
            EXPECT_FALSE(res.has_error());
        }
        else {
            ASSERT_TRUE(res.has_error());
            EXPECT_EQ(
                res.error(), MonadBlockError::SystemTransactionOutOfOrder);
        }
    }
}

TYPED_TEST(MonadTraitsTest, duplicate_syscalls_error)
{
    using Trait = typename TestFixture::Trait;

    std::vector<std::vector<uint32_t>> const orders{
        {SNAPSHOT, SNAPSHOT},
        {ON_EPOCH_CHANGE, ON_EPOCH_CHANGE},
        {REWARD, REWARD},
        {SNAPSHOT, SNAPSHOT, ON_EPOCH_CHANGE},
        {SNAPSHOT, ON_EPOCH_CHANGE, ON_EPOCH_CHANGE},
        {ON_EPOCH_CHANGE, ON_EPOCH_CHANGE, REWARD},
        {SNAPSHOT, REWARD, REWARD},
    };

    for (auto const &order : orders) {
        auto const senders = system_senders(order.size());
        auto const txns = system_txns(order);
        auto const res = static_validate_monad_body<Trait>(senders, txns);
        if constexpr (Trait::monad_rev() < MONAD_FOUR) {
            EXPECT_FALSE(res.has_error());
        }
        else {
            ASSERT_TRUE(res.has_error());
            EXPECT_EQ(res.error(), MonadBlockError::DuplicateSystemTransaction);
        }
    }
}

TYPED_TEST(MonadTraitsTest, unknown_syscall_error)
{
    using Trait = typename TestFixture::Trait;

    std::vector<byte_string> const datas{
        syscall_calldata(0xdeadbeef),
        byte_string{},
        byte_string{0x15, 0x7e, 0xeb},
    };

    for (auto const &data : datas) {
        auto const senders = system_senders(1);
        std::vector<Transaction> txns(1);
        txns[0].data = data;
        auto const res = static_validate_monad_body<Trait>(senders, txns);
        if constexpr (Trait::monad_rev() < MONAD_FOUR) {
            EXPECT_FALSE(res.has_error());
        }
        else {
            ASSERT_TRUE(res.has_error());
            EXPECT_EQ(res.error(), MonadBlockError::UnknownSystemTransaction);
        }
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
    txns[0].data = syscall_calldata(REWARD);
    txns[0].value = 26 * staking::MON;
    auto const res = static_validate_monad_body<Trait>(senders, txns);
    if constexpr (Trait::monad_rev() < MONAD_FOUR) {
        EXPECT_FALSE(res.has_error());
    }
    else {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), MonadBlockError::InvalidRewardValue);
    }
}

TYPED_TEST(MonadTraitsTest, mip12_migration)
{
    using Trait = typename TestFixture::Trait;

    std::vector<Address> senders{
        SYSTEM_SENDER,
    };
    std::vector<Transaction> txns(senders.size());
    // 25 MON is staking reward before MIP-12
    txns[0].data = syscall_calldata(REWARD);
    txns[0].value = 25 * staking::MON;
    auto const res = static_validate_monad_body<Trait>(senders, txns);
    if constexpr (Trait::mip_12_active()) {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), MonadBlockError::InvalidRewardValue);
    }
    else {
        EXPECT_FALSE(res.has_error());
    }
}

// Fork-independent tests pinned to the latest revision.
using ValidateMonadBlockLatest =
    MonadTraitsTest<::detail::MonadRevisionConstant<MONAD_NEXT>>;

struct RewardCase
{
    uint256_t value;
    bool expect_error;
    std::string_view name;
};

class BlockRewardLatest
    : public ValidateMonadBlockLatest
    , public ::testing::WithParamInterface<RewardCase>
{
};

// maximum_block_reward is 18 MON once MIP-12 is active (latest revision).
INSTANTIATE_TEST_SUITE_P(
    Mip12, BlockRewardLatest,
    ::testing::Values(
        RewardCase{0, false, "zero"},
        RewardCase{1 * staking::MON, false, "one_mon"},
        RewardCase{18 * staking::MON, false, "at_maximum"},
        RewardCase{18 * staking::MON + 1, true, "one_wei_over"},
        RewardCase{25 * staking::MON, true, "pre_mip_12_maximum"},
        RewardCase{26 * staking::MON, true, "exceeds_one"},
        RewardCase{100 * staking::MON, true, "well_over"}),
    [](::testing::TestParamInfo<RewardCase> const &info) {
        return std::string{info.param.name};
    });

TEST_P(BlockRewardLatest, reward_against_maximum)
{
    auto const &param = GetParam();

    std::vector<Address> senders{
        SYSTEM_SENDER,
    };
    std::vector<Transaction> txns(senders.size());
    txns[0].data = syscall_calldata(REWARD);
    txns[0].value = param.value;

    auto const res = static_validate_monad_body<Trait>(senders, txns);
    if (param.expect_error) {
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(res.error(), MonadBlockError::InvalidRewardValue);
    }
    else {
        EXPECT_FALSE(res.has_error());
    }
}
