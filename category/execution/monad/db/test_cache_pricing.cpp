// Copyright (C) 2026 Category Labs, Inc.
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
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstdint>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    using MbcFork = MonadTraits<MONAD_NEXT>;
    static_assert(MbcFork::multi_block_cache_active());

    constexpr auto slot_0 = bytes32_t{uint64_t{0x00}};
    constexpr auto slot_1 = bytes32_t{uint64_t{0x01}};

    Code const empty_code{};
    std::vector<Receipt> const empty_receipts{};
    std::vector<Transaction> const empty_transactions{};
    std::vector<Address> const empty_senders{};
    std::vector<std::vector<CallFrame>> const empty_call_frames{};
    std::vector<BlockHeader> const empty_ommers{};
    std::optional<std::vector<Withdrawal>> const empty_withdrawals{};

    void drive_commit(
        TrieDb &tdb, uint64_t const block_number,
        uint64_t const parent_number, bytes32_t const &parent_id,
        StateDeltas const &deltas, BlockAccessSets const &access)
    {
        tdb.set_block_and_prefix(parent_number, parent_id);
        BlockHeader const header{.number = block_number};
        BlockCommitAncillaries const anc{
            .code = empty_code,
            .receipts = empty_receipts,
            .transactions = empty_transactions,
            .senders = empty_senders,
            .call_frames = empty_call_frames,
            .ommers = empty_ommers,
            .withdrawals = empty_withdrawals,
            .access = &access};
        commit_block<MbcFork>(
            tdb, nullptr, bytes32_t{block_number}, header, deltas, anc);
        tdb.finalize(block_number, bytes32_t{block_number});
    }
}

TEST(CachePricing, bucket_key)
{
    auto const key =
        cache_pricing_bucket_key(PricingKind::storage, 0x0102030405060708);
    ASSERT_EQ(key.size(), 9);
    EXPECT_EQ(key[0], 1);
    EXPECT_EQ(key[1], 0x01);
    EXPECT_EQ(key[8], 0x08);
}

TEST(CachePricing, last_access_bump_and_histogram)
{
    mpt::Db db{std::make_unique<MonadOnDiskMachine>(), mpt::OnDiskDbConfig{}};
    TrieDb tdb{db};
    ASSERT_TRUE(tdb.is_page_encoded());

    GenesisState const GENESIS_STATE = MonadTestnet{}.get_genesis_state();
    load_genesis_state(GENESIS_STATE, tdb);

    auto const page_key = compute_page_key(slot_0);
    ASSERT_EQ(page_key, compute_page_key(slot_1));

    BlockAccessSets access;
    access[ADDR_A].insert(page_key);

    // block 1: create account, write two slots on one page
    Account const created{.nonce = 1};
    {
        StorageDeltas storage;
        storage.emplace(
            slot_0, StorageDelta{bytes32_t{}, bytes32_t{uint64_t{0xa1}}});
        storage.emplace(
            slot_1, StorageDelta{bytes32_t{}, bytes32_t{uint64_t{0xb1}}});
        StateDeltas deltas;
        deltas.emplace(
            ADDR_A,
            StateDelta{
                .account = {std::nullopt, created},
                .storage = std::move(storage)});
        drive_commit(tdb, 1, 0, bytes32_t{}, deltas, access);
    }

    tdb.set_block_and_prefix(1, bytes32_t{uint64_t{1}});
    auto const acct1 = tdb.read_account(ADDR_A);
    ASSERT_TRUE(acct1.has_value());
    EXPECT_EQ(acct1->last_access_block, 1);
    auto const page1 =
        tdb.read_storage_page(ADDR_A, acct1->incarnation, page_key);
    EXPECT_EQ(page1.last_access, 1);
    EXPECT_EQ(tdb.read_account_pricing_bucket(1), 1);
    EXPECT_EQ(tdb.read_storage_pricing_bucket(1), 2);

    // block 2: read-only touch within C, no bump and no histogram change
    {
        StateDeltas deltas;
        deltas.emplace(
            ADDR_A, StateDelta{.account = {acct1, acct1}, .storage = {}});
        drive_commit(tdb, 2, 1, bytes32_t{uint64_t{1}}, deltas, access);
    }
    tdb.set_block_and_prefix(2, bytes32_t{uint64_t{2}});
    EXPECT_EQ(tdb.read_account(ADDR_A)->last_access_block, 1);
    EXPECT_EQ(tdb.read_account_pricing_bucket(1), 1);
    EXPECT_EQ(tdb.read_account_pricing_bucket(2), std::nullopt);

    // read-only touch every block; the bump lands exactly at block 1 + C
    uint64_t const bump_block = 1 + CACHE_PRICING_UPDATE_INTERVAL;
    for (uint64_t b = 3; b <= bump_block; ++b) {
        StateDeltas deltas;
        deltas.emplace(
            ADDR_A, StateDelta{.account = {acct1, acct1}, .storage = {}});
        drive_commit(tdb, b, b - 1, bytes32_t{b - 1}, deltas, access);
        if (b < bump_block) {
            tdb.set_block_and_prefix(b, bytes32_t{b});
            EXPECT_EQ(tdb.read_account(ADDR_A)->last_access_block, 1);
        }
    }
    tdb.set_block_and_prefix(bump_block, bytes32_t{bump_block});
    auto const acct2 = tdb.read_account(ADDR_A);
    EXPECT_EQ(acct2->last_access_block, bump_block);
    auto const page2 =
        tdb.read_storage_page(ADDR_A, acct2->incarnation, page_key);
    EXPECT_EQ(page2.last_access, bump_block);
    EXPECT_EQ(page2[0], bytes32_t{uint64_t{0xa1}});
    EXPECT_EQ(
        tdb.read_account_pricing_bucket(1), std::nullopt);
    EXPECT_EQ(tdb.read_account_pricing_bucket(bump_block), 1);
    EXPECT_EQ(
        tdb.read_storage_pricing_bucket(1), std::nullopt);
    EXPECT_EQ(tdb.read_storage_pricing_bucket(bump_block), 2);

    // young chain, weight below capacity: everything in the window is cached
    auto const cutoffs = compute_pricing_cutoffs(tdb, bump_block + 1);
    EXPECT_EQ(cutoffs.account, 0);
    EXPECT_EQ(cutoffs.storage, 0);
}

TEST(CachePricing, no_access_no_change)
{
    mpt::Db db{std::make_unique<MonadOnDiskMachine>(), mpt::OnDiskDbConfig{}};
    TrieDb tdb{db};

    GenesisState const GENESIS_STATE = MonadTestnet{}.get_genesis_state();
    load_genesis_state(GENESIS_STATE, tdb);

    // written but absent from the access set (aborted speculative read
    // pollution shape): value committed, no bump, no histogram entry
    BlockAccessSets const empty_access;
    Account const created{.nonce = 1};
    {
        StateDeltas deltas;
        deltas.emplace(
            ADDR_A,
            StateDelta{.account = {std::nullopt, created}, .storage = {}});
        drive_commit(tdb, 1, 0, bytes32_t{}, deltas, empty_access);
    }
    tdb.set_block_and_prefix(1, bytes32_t{uint64_t{1}});
    EXPECT_EQ(tdb.read_account(ADDR_A)->last_access_block, 0);
    EXPECT_EQ(tdb.read_account_pricing_bucket(1), std::nullopt);
}
