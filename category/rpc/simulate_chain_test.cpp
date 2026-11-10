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

#include <category/core/monad_exception.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/rpc/simulate_chain.hpp>
#include <category/vm/evm/revision.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <memory>
#include <string_view>

using namespace monad;

namespace
{
    constexpr uint64_t max_u64 = std::numeric_limits<uint64_t>::max();

    char const stub_alloc[] = "stub alloc";

    struct StubChain final : Chain
    {
        uint256_t get_chain_id() const override
        {
            return 1234;
        }

        EvmRevision get_revision(uint64_t, uint64_t) const override
        {
            return EvmRevision::Berlin;
        }

        BlobSchedule get_blob_schedule(uint64_t) const override
        {
            return BlobSchedule{
                .target_blobs_per_block = 1,
                .max_blobs_per_block = 2,
                .blob_base_fee_update_fraction = 3};
        }

        GenesisState get_genesis_state() const override
        {
            return GenesisState{
                .header = BlockHeader{.number = 42}, .alloc = stub_alloc};
        }
    };

    void expect_blob_schedule_eq(
        BlobSchedule const &actual, BlobSchedule const &expected)
    {
        EXPECT_EQ(
            actual.target_blobs_per_block, expected.target_blobs_per_block);
        EXPECT_EQ(actual.max_blobs_per_block, expected.max_blobs_per_block);
        EXPECT_EQ(
            actual.blob_base_fee_update_fraction,
            expected.blob_base_fee_update_fraction);
    }
}

TEST(SimulateEvmChain, is_supported_revision)
{
    for (auto const rev :
         {EvmRevision::Berlin,
          EvmRevision::London,
          EvmRevision::Paris,
          EvmRevision::Shanghai,
          EvmRevision::Cancun,
          EvmRevision::Prague,
          EvmRevision::Osaka,
          EvmRevision::Amsterdam}) {
        EXPECT_TRUE(SimulateEvmChain::is_supported_revision(rev))
            << std::to_underlying(rev);
    }
    for (auto const rev :
         {EvmRevision::Frontier,
          EvmRevision::Istanbul,
          EvmRevision::Experimental}) {
        EXPECT_FALSE(SimulateEvmChain::is_supported_revision(rev))
            << std::to_underlying(rev);
    }
}

TEST(SimulateEvmChain, overrides_revision_and_blob_schedule)
{
    SimulateEvmChain const chain{
        std::make_unique<StubChain>(), EvmRevision::Prague};

    EXPECT_EQ(chain.get_revision(0, 0), EvmRevision::Prague);
    EXPECT_EQ(chain.get_revision(max_u64, max_u64), EvmRevision::Prague);
    expect_blob_schedule_eq(chain.get_blob_schedule(0), PRAGUE_BLOB_SCHEDULE);
    expect_blob_schedule_eq(
        chain.get_blob_schedule(max_u64), PRAGUE_BLOB_SCHEDULE);
}

TEST(SimulateEvmChain, delegates_chain_id_and_genesis_state)
{
    SimulateEvmChain const chain{
        std::make_unique<StubChain>(), EvmRevision::Cancun};

    EXPECT_EQ(chain.get_chain_id(), uint256_t{1234});
    auto const genesis = chain.get_genesis_state();
    EXPECT_EQ(genesis.header, BlockHeader{.number = 42});
    EXPECT_EQ(genesis.alloc, stub_alloc);
}

// Mainnet derives a pre-Berlin fork from the ethereum-tests environment (block
// 1 at timestamp 1000) and a BPO2 blob schedule from far-future timestamps;
// pinning makes both follow the pinned fork.
TEST(SimulateEvmChain, ethereum_mainnet_at_test_environment)
{
    SimulateEvmChain const chain{
        std::make_unique<EthereumMainnet>(), EvmRevision::Cancun};

    EXPECT_EQ(chain.get_chain_id(), uint256_t{1});
    EXPECT_EQ(chain.get_revision(1, 1000), EvmRevision::Cancun);
    expect_blob_schedule_eq(
        chain.get_blob_schedule(1000), CANCUN_BLOB_SCHEDULE);
    expect_blob_schedule_eq(
        chain.get_blob_schedule(max_u64), CANCUN_BLOB_SCHEDULE);
}

namespace
{
    template <typename F>
    void expect_monad_exception(F const &f, std::string_view const expected)
    {
        try {
            f();
            ADD_FAILURE() << "expected MonadException: " << expected;
        }
        catch (MonadException const &e) {
            EXPECT_EQ(std::string_view{e.message()}, expected);
        }
    }
}

TEST(SimulateEvmChain, rejects_null_chain)
{
    expect_monad_exception(
        [] { SimulateEvmChain{nullptr, EvmRevision::Cancun}; },
        "inner chain must not be null");
}

TEST(SimulateEvmChain, rejects_monad_chain)
{
    expect_monad_exception(
        [] {
            SimulateEvmChain{
                std::make_unique<MonadDevnet>(), EvmRevision::Cancun};
        },
        "inner chain must not be a MonadChain");
}

TEST(SimulateEvmChain, rejects_unsupported_revision)
{
    expect_monad_exception(
        [] {
            SimulateEvmChain{
                std::make_unique<StubChain>(), EvmRevision::Istanbul};
        },
        "unsupported EVM revision");
}
