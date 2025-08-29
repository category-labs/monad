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

#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/read_valset.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <test_resource_data.h>
#include <utility>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::staking;

namespace
{
    constexpr uint64_t TEST_BLOCK_NUM = 0;
    constexpr uint64_t TEST_EPOCH = 100;
    constexpr uint64_t SNAPSHOT_VALSET_LENGTH = 5;
    constexpr uint64_t CONSENSUS_VALSET_LENGTH = 10;
    constexpr uint256_t SNAPSHOT_STAKE = 100_u256;
    constexpr uint256_t CONSENSUS_STAKE = 300_u256;

    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "staking_read_valset_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        OnDiskMachine machine;
        mpt::Db const db{
            machine,
            mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
        return dbname;
    }
}

class ReadValsetBase : public ::testing::Test
{
protected:
    std::filesystem::path dbname;
    mpt::AsyncIOContext io_ctx;
    mpt::Db ro;

    ReadValsetBase()
        : dbname{tmp_dbname()}
        , io_ctx{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}}
        , ro{io_ctx}

    {
    }

    void SetUp() override
    {
        OnDiskMachine machine;
        vm::VM vm;
        mpt::Db db{machine, mpt::OnDiskDbConfig{.dbname_paths = {dbname}}};
        TrieDb tdb{db};
        BlockState bs{tdb, vm};
        State state{bs, Incarnation{0, 0}};
        StakingContract contract{state};

        state.add_to_balance(STAKING_CA, 0);

        // push the consensus and snapshot valsets. they have different lengths
        // so they can easily be identified.
        for (uint64_t id = 1; id <= SNAPSHOT_VALSET_LENGTH; ++id) {
            contract.vars.valset_snapshot.push(id);
            contract.vars.snapshot_view(id).stake().store(SNAPSHOT_STAKE);
        }
        for (uint64_t id = 1; id <= CONSENSUS_VALSET_LENGTH; ++id) {
            contract.vars.valset_consensus.push(id + SNAPSHOT_VALSET_LENGTH);
            contract.vars.consensus_view(id + SNAPSHOT_VALSET_LENGTH)
                .stake()
                .store(CONSENSUS_STAKE);
        }

        contract.vars.epoch.store(TEST_EPOCH);
        contract.vars.in_epoch_delay_period.store(in_epoch_delay_period());

        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
        bs.commit(
            NULL_HASH_BLAKE3,
            BlockHeader{.number = TEST_BLOCK_NUM},
            {},
            {},
            {},
            {},
            {},
            {});
        tdb.finalize(TEST_BLOCK_NUM, NULL_HASH_BLAKE3);
    }

    virtual bool in_epoch_delay_period() const = 0;
};

class ReadValsetBeforeBoundary : public ReadValsetBase
{
    bool in_epoch_delay_period() const override
    {
        return false;
    }
};

TEST_F(ReadValsetBeforeBoundary, get_this_epoch_valset)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH);
    ASSERT_TRUE(set.has_value());
    EXPECT_EQ(set.value().size(), CONSENSUS_VALSET_LENGTH);
    for (auto const &validator : set.value()) {
        EXPECT_EQ(intx::be::load<uint256_t>(validator.stake), CONSENSUS_STAKE);
    }
}

TEST_F(ReadValsetBeforeBoundary, get_next_epoch_valset)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH + 1);
    EXPECT_FALSE(set.has_value());
}

TEST_F(ReadValsetBeforeBoundary, asking_for_expired_epoch)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH - 1);
    ASSERT_FALSE(set.has_value());
}

TEST_F(ReadValsetBeforeBoundary, asking_for_future_epoch)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH + 3);
    ASSERT_FALSE(set.has_value());
}

class ReadValsetAfterBoundary : public ReadValsetBase
{
    bool in_epoch_delay_period() const override
    {
        return true;
    }
};

TEST_F(ReadValsetAfterBoundary, get_this_epoch_valset)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH);

    // expect the snapshot view when requesting current epoch valset
    ASSERT_TRUE(set.has_value());
    EXPECT_EQ(set.value().size(), SNAPSHOT_VALSET_LENGTH);
    for (auto const &validator : set.value()) {
        EXPECT_EQ(intx::be::load<uint256_t>(validator.stake), SNAPSHOT_STAKE);
    }
}

TEST_F(ReadValsetAfterBoundary, get_next_epoch_valset)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH + 1);

    // expect the consensus view when requesting current epoch valset
    ASSERT_TRUE(set.has_value());
    EXPECT_EQ(set.value().size(), CONSENSUS_VALSET_LENGTH);
    for (auto const &validator : set.value()) {
        EXPECT_EQ(intx::be::load<uint256_t>(validator.stake), CONSENSUS_STAKE);
    }
}

TEST_F(ReadValsetAfterBoundary, asking_for_expired_epoch)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH - 1);
    EXPECT_FALSE(set.has_value());
}

TEST_F(ReadValsetAfterBoundary, asking_for_future_epoch)
{
    auto const set = read_valset(ro, TEST_BLOCK_NUM, TEST_EPOCH + 3);
    EXPECT_FALSE(set.has_value());
}
